module Parser where
import Base
import Ast

-- Parser for Idris-style syntax.
-- Supports both Haskell (->) and Idris (=>) style arrows.

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

ident = lexeme $ do
  c <- satisfy (\c -> isAlpha c || c == '_')
  cs <- many (satisfy (\c -> isAlphaNum c || c == '_' || c == '\''))
  let name = c:cs
  if elem name ["data", "where", "let", "in", "case", "of", "if", "then", "else", "do", "module", "import", "interface", "implementation", "record", "infix", "infixl", "infixr", "total", "partial", "Type", "using", "namespace", "mutual", "parameters", "public", "private", "export", "covering", "impossible", "with", "proof", "rewrite", "auto", "default", "ifx", "postfix"]
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

-- Term parsing.
parseTerm = parseExpr

parseExpr = parsePiSigma <|> parseLambda <|> parseLet <|> parseIf <|> parseCase <|> parseDo <|> parseApp

parsePiSigma = do
  token "("
  v <- ident
  token ":"
  ty <- parseTerm
  (token "->" <|> token "=>")
  body <- parseTerm
  token ")"
  pure $ Pi (Raw v) ty body

parseLambda = do
  token "\\"
  vars <- some ident
  (token "->" <|> token "=>")
  body <- parseTerm
  pure $ foldr (\v t -> Lam (Raw v) t) body vars

parseLet = do
  keyword "let"
  v <- ident
  token "="
  val <- parseTerm
  keyword "in"
  body <- parseTerm
  pure $ Let (Raw v) val body

parseIf = do
  keyword "if"
  cond <- parseTerm
  keyword "then"
  t <- parseTerm
  keyword "else"
  e <- parseTerm
  pure $ Case cond [(PCon "True" [], t), (PCon "False" [], e)]

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
  pure (pat, rhs)

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
desugarDo (Left (v, m) : rest) = App (App (Var (Raw ">>=")) m) (Lam (Raw v) (desugarDo rest))
desugarDo (Right e : rest) = App (App (Var (Raw ">>") e) (desugarDo rest))

parseApp = do
  atoms <- some parseAtom
  pure $ foldl1 App atoms

parseAtom = parseVar <|> parseNatLit <|> parseCharLit <|> parseStringLit <|> parseParen <|> parseType <|> parseRefl <|> parsePair <|> parseProj

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
  pure $ foldr (\c t -> App (App (Var (Global "Cons")) (CharLit (ord c))) t) (Var (Global "Nil")) cs

parseParen = parens parseTerm
parseType = keyword "Type" *> (token (string (show i)) *> pure (Type i) <|> pure (Type 0))
parseRefl = keyword "Refl" *> (Refl <$> parseTerm <|> pure (Refl (Var (Raw "_"))))
parsePair = parens $ do
  a <- parseTerm
  token ","
  b <- parseTerm
  pure $ Pair a b

parseProj = do
  tok <- keyword "fst" <|> keyword "snd"
  e <- parseAtom
  pure $ case tok of "fst" -> Proj1 e; _ -> Proj2 e

-- Declaration parsing.
parseDecl = parseDataDecl <|> parseTypeSig <|> parseFunDef <|> parseFixityDecl

parseDataDecl = do
  keyword "data"
  name <- ident
  token "="
  cs <- sepBy1 parseCon (token "|")
  pure $ DataDecl name cs

parseCon = do
  c <- ident
  ts <- many parseAtom
  pure (c, ts)

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
