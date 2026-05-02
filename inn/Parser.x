module Parser where
import Base
import Ast

-- ============================================
-- CIC PARSER: Idris/Lean-style syntax
-- Supports: inductive families, universe levels, implicit args
-- ============================================

data Pos = Pos Int Int deriving (Eq, Show)
incCol (Pos l c) = Pos l (c+1)
incLine (Pos l _) = Pos (l+1) 1)
initialPos = Pos 1 1

data ParseState = ParseState { source :: String, pos :: Pos }

data Parser a = Parser (ParseState -> [(a, ParseState)])

instance Functor Parser where
  fmap f (Parser p) = Parser \s -> map (\(x, s') -> (f x, s')) (p s)

instance Applicative Parser where
  pure x = Parser \s -> [(x, s)]
  Parser pf <*> Parser px = Parser \s -> concatMap (\(f, s') -> map (\(x, s'') -> (f x, s'')) (px s')) (pf s)

instance Monad Parser where
  return = pure
  Parser p >>= f = Parser \s -> concatMap (\(x, s') -> let Parser p' = f x in p' s') (p s)

instance Alternative Parser where
  empty = Parser (const [])
  Parser p1 <|> Parser p2 = Parser \s -> case p1 s of
    [] -> p2 s
    rs -> rs

runParser (Parser p) src = case p (ParseState src initialPos) of
  [] -> Left "Parse error"
  ((x, s):_) -> if null (source s) then Right x else Left $ "Unexpected: " ++ take 20 (source s)

satisfy f = Parser \s -> case source s of
  (c:cs) | f c -> [(c, s { source = cs, pos = incCol (pos s) })]
  _ -> []

char c = satisfy (== c)
string "" = pure ""
string (c:cs) = (:) <$> char c <*> string cs

space = satisfy isSpace
spaces = many space
lexeme p = p <* spaces
token s = lexeme (string s)

parens p = between (char '(') (char ')') p
braces p = between (char '{') (char '}') p
brackets p = between (char '[') (char ']') p

-- Identifiers
ident = lexeme $ do
  c <- satisfy (\c -> isAlpha c || c == '_')
  cs <- many (satisfy (\c -> isAlphaNum c || c == '_' || c == '\''))
  let name = c:cs
  if elem name ["data", "where", "let", "in", "case", "of", "if", "then", "else", "do", "module", "import", "axiom", "inductive", "using", "namespace", "mutual", "parameters", "public", "private", "export", "impossible", "with", "rewrite", "auto", "default", "Sort", "Prop", "Type"]
    then empty
    else pure name

keyword s = lexeme $ string s *> notFollowedBy (satisfy isAlphaNum)

notFollowedBy p = Parser \s -> case runParser p (source s) of
  Left _ -> [((), s)]
  Right _ -> []

sepBy p sep = (:) <$> p <*> many (sep *> p) <|> pure []
sepBy1 p sep = (:) <$> p <*> many (sep *> p)
endBy p sep = many (p <* sep)
endBy1 p sep = some (p <* sep)

-- ============================================
-- TERM PARSING
-- ============================================
parseTerm = parseExpr

parseExpr = parsePiSigma <|> parseLambda <|> parseLet <|> parseIf <|> parseCase <|> parseDo <|> parseApp

-- Parse Pi type: (x : A) -> B or {x : A} -> B (implicit)
parsePiSigma = do
  (implicit, b) <- parseBinderIntro
  case b of
    Just (name, ty) -> do
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ if implicit
        then Pi (BImplicit (Raw name) ty) body
        else Pi (BExplicit (Raw name) ty) body
    Nothing -> empty

parseBinderIntro = do
  -- try implicit {x : A}
  implicit <- (token "{" *> pure True) <|> (token "(" *> pure False)
  v <- ident
  token ":"
  ty <- parseTerm
  (if implicit then token "}" else token ")")
  pure (implicit, Just (v, ty))
  <|> pure (False, Nothing)

parseLambda = do
  token "\\"
  (implicit, binderInfo) <- parseBinderIntro
  case binderInfo of
    Just (v, ty) -> do
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ if implicit
        then Lam (BImplicit (Raw v) ty) body
        else Lam (BExplicit (Raw v) ty) body
    Nothing -> do
      vars <- some ident
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ foldr (\v t -> Lam (BExplicit (Raw v) (Hole "_")) t) body vars

parseLet = do
  keyword "let"
  v <- ident
  token ":"
  ty <- parseTerm
  token "="
  val <- parseTerm
  keyword "in"
  body <- parseTerm
  pure $ Let (Raw v) ty val body

parseIf = do
  keyword "if"
  cond <- parseTerm
  keyword "then"
  t <- parseTerm
  keyword "else"
  e <- parseTerm
  pure $ Case cond [(Clause (PCon "True" []) t), (Clause (PCon "False" []) e)]

parseCase = do
  keyword "case"
  e <- parseTerm
  keyword "of"
  token "{"
  alts <- sepBy parseAlt (token ";")
  token "}"
  pure $ Case e alts

parseAlt = do
  pat <- parsePattern
  token "=>"
  rhs <- parseTerm
  pure (Clause pat rhs)

parsePattern = parsePCon <|> parsePLit <|> parsePVar
parsePVar = PVar . Raw <$> ident
parsePLit = PLit <$> parseNat
parsePCon = do
  c <- ident
  ps <- many parsePattern
  pure $ PCon c ps

parseDo = do
  keyword "do"
  token "{"
  stmts <- sepBy parseStmt (token ";")
  token "}"
  pure $ desugarDo stmts

parseStmt = do
  v <- ident
  token "<-"
  m <- parseTerm
  pure $ Left (v, m)
  <|> do
  e <- parseTerm
  pure $ Right e

desugarDo [] = Var (Raw "return")
desugarDo [Right e] = e
desugarDo (Left (v, m) : rest) = App (App (Var (Raw ">>=")) m) (Lam (BExplicit (Raw v) (Hole "_")) (desugarDo rest))
desugarDo (Right e : rest) = App (App (Var (Raw ">>")) e) (desugarDo rest)

parseApp = do
  atoms <- some parseAtom
  pure $ foldl1 App atoms

parseAtom = parseVar <|> parseNatLit <|> parseCharLit <|> parseStringLit <|> parseParen <|> parseSort <|> parseRefl <|> parsePair <|> parseProj

parseVar = Var . Raw <$> ident
parseNatLit = NatLit <$> lexeme (readNat <$> some (satisfy isDigit))
  where readNat cs = foldl (\n c -> n*10 + ord c - ord '0') 0 cs

parseCharLit = do
  token "'"
  c <- satisfy (const True)
  token "'"
  pure $ CharLit (ord c)

parseStringLit = do
  token "\""
  cs <- many (satisfy (\c -> c /= '"'))
  token "\""
  pure $ StringLit cs

parseParen = parens parseTerm

-- Sort parsing: Prop, Type, Type u, Sort u
parseSort = parseProp <|> parseType <|> parseSortKw

parseProp = keyword "Prop" *> pure (Sort SProp)

parseType = do
  keyword "Type"
  (token (string (show i)) *> pure (Sort (SType (NatLit i))) <|> pure (Sort (SType LZero)))
  -- Simplified: just parse "Type" as Type 0
  where i = 0

parseSortKw = keyword "Sort" *> (Sort . SType <$> parseLevel)

parseLevel = parseLZero <|> parseLSucc <|> parseLMax
parseLZero = token "0" *> pure LZero
parseLSucc = token "succ" *> (LSucc <$> parseLevel)
parseLMax = token "max" *> (LMax <$> parseLevel <*> parseLevel)

parseRefl = keyword "Refl" *> (Refl <$> parseTerm <|> pure (Refl (Var (Raw "_"))))

parsePair = parens $ do
  a <- parseTerm
  token ","
  b <- parseTerm
  pure $ Pair a b

parseProj = do
  tok <- keyword "fst" <|> keyword "snd"
  e <- parseAtom
  pure $ case tok of "fst" -> Proj 1 e; _ -> Proj 2 e

-- ============================================
-- DECLARATION PARSING
-- ============================================
parseDecl = parseIndDecl <|> parseTypeSig <|> parseFunDef <|> parseAxiomDecl <|> parseFixityDecl

-- Inductive family: data D (a : Type) : Type -> Type where | C1 : ... | C2 : ...
parseIndDecl = do
  keyword "data"
  name <- ident
  params <- many parseParam
  token ":"
  targetSort <- parseSort
  keyword "where"
  token "{"
  constrs <- sepBy1 parseConstrDecl (token "|")
  token "}"
  let indices = extractIndices params targetSort
  let indDef = IndDef
    { indName = name
    , indParams = take (length params - length indices) params
    , indIndices = indices
    , indSort = case targetSort of Sort s -> s; _ -> SType LZero
    , indConstrs = constrs
    }
  pure $ IndDecl indDef

parseParam = do
  token "("
  v <- ident
  token ":"
  ty <- parseTerm
  token ")"
  pure $ BExplicit (Raw v) ty
  <|> do
  token "{"
  v <- ident
  token ":"
  ty <- parseTerm
  token "}"
  pure $ BImplicit (Raw v) ty

parseConstrDecl = do
  c <- ident
  token ":"
  ty <- parseTerm
  -- parse constructor type: parameters already applied, rest are args + result indices
  let (args, result) = splitConstrType ty
  pure $ ConstrDef
    { conName = c
    , conArgs = args
    , conResult = result
    }

splitConstrType :: Term -> ([Binder], [Term])
splitConstrType ty = ([], [])  -- TODO: proper splitting

extractIndices :: [Binder] -> Term -> [Binder]
extractIndices params target = []  -- TODO: extract indices from target type

parseTypeSig = do
  name <- ident
  token ":"
  ty <- parseTerm
  pure $ TypeSig name ty

parseFunDef = do
  name <- ident
  clauses <- some parseClause
  pure $ FunDef name clauses

parseClause = do
  ps <- some parsePattern
  token "="
  rhs <- parseTerm
  pure $ Clause ps rhs

parseAxiomDecl = do
  keyword "axiom"
  name <- ident
  token ":"
  ty <- parseTerm
  pure $ AxiomDecl name ty

parseFixityDecl = do
  f <- (keyword "infix" *> pure Infix) <|> (keyword "infixl" *> pure InfixL) <|> (keyword "infixr" *> pure InfixR)
  prec <- lexeme (readNat <$> some (satisfy isDigit))
  ops <- some ident
  pure $ InfixDecl f prec ops

parseModule = do
  keyword "module"
  name <- ident
  keyword "where"
  decls <- many parseDecl
  pure decls

parseFile src = runParser (spaces *> (parseModule <|> many parseDecl) <* spaces) src
