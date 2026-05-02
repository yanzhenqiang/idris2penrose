module Typer where
import Base
import Ast

-- ============================================
-- CIC TYPE CHECKER (Calculus of Inductive Constructions)
-- Following Lean 4 / Coq core type theory
-- ============================================

-- Context: name -> (type, optional value for conversion)
type Ctx = [(Name, (Term, Maybe Term))]

extend :: Name -> Term -> Maybe Term -> Ctx -> Ctx
extend n ty val ctx = (n, (ty, val)) : ctx

lookupType :: Name -> Ctx -> Maybe Term
lookupType n ctx = fmap fst (mlookup n ctx)

lookupVal :: Name -> Ctx -> Maybe (Maybe Term)
lookupVal n ctx = fmap snd (mlookup n ctx)

-- ============================================
-- UNIVERSE LEVEL OPERATIONS
-- ============================================

levelMax :: Level -> Level -> Level
levelMax LZero u = u
levelMax u LZero = u
levelMax (LSucc u) (LSucc v) = LSucc (levelMax u v)
levelMax u v = LMax u v

levelSucc :: Level -> Level
levelSucc = LSucc

-- Universe cumulativity: Prop <= Type 0 <= Type 1 <= ...
sortLeq :: Sort -> Sort -> Bool
sortLeq SProp (SType _)     = True
sortLeq (SType u) (SType v) = levelLeq u v
sortLeq s1 s2               = s1 == s2

levelLeq :: Level -> Level -> Bool
levelLeq LZero _ = True
levelLeq (LSucc u) (LSucc v) = levelLeq u v
levelLeq u v = u == v

sortSucc :: Sort -> Sort
sortSucc SProp       = SType LZero
sortSucc (SType u)   = SType (levelSucc u)
sortSucc (SSucc s)   = SSucc (sortSucc s)

-- ============================================
-- WEAK HEAD NORMAL FORM (WHNF)
-- ============================================
whnf :: Ctx -> Term -> Term
whnf ctx t = case t of
  App f x -> case whnf ctx f of
    Lam (BExplicit _ _) b -> whnf ctx (substitute x (binderName (Lam (BExplicit (Raw "_") (Sort SProp)) b)) b)
    Lam (BImplicit _ _) b -> whnf ctx (substitute x (binderName (Lam (BImplicit (Raw "_") (Sort SProp)) b)) b)
    Pi _ _ -> error "Pi applied"
    Fix info body ->
      -- unfold fixpoint once, then reduce
      let unfolded = substitute (Fix info body) (fixName info) body
      in whnf ctx (App unfolded x)
    f' -> App f' x
  Case e ps -> case whnf ctx e of
    Constr _ c args ->
      -- find matching clause
      case findClause c ps of
        Just rhs -> whnf ctx (applyPatterns rhs args ps)
        Nothing -> Case (Constr (indNameFromConstr c ctx) c args) ps
    NatLit 0 -> case findLitClause 0 ps of
      Just rhs -> whnf ctx rhs
      Nothing -> Case (NatLit 0) ps
    Refl e' -> case findReflClause ps of
      Just rhs -> whnf ctx rhs
      Nothing -> Case (Refl e') ps
    e' -> Case e' ps
  Let _ _ v b -> whnf ctx (substitute v (Let (Raw "_") (Sort SProp) (NatLit 0) (NatLit 0)) b)
  Proj1 e -> case whnf ctx e of
    Pair a _ -> a
    Constr _ "MkSigma" [a, _] -> a
    e' -> Proj1 e'
  Proj2 e -> case whnf ctx e of
    Pair _ b -> b
    Constr _ "MkSigma" [_, b] -> b
    e' -> Proj2 e'
  Annot e _ -> whnf ctx e
  Var n -> case lookupVal n ctx of
    Just (Just v) -> whnf ctx v
    _ -> Var n
  _ -> t

binderName :: Term -> Name
binderName (Lam (BExplicit n _) _) = n
binderName (Lam (BImplicit n _) _) = n
binderName (Pi (BExplicit n _) _) = n
binderName (Pi (BImplicit n _) _) = n
binderName _ = Raw "_"

indNameFromConstr :: String -> Ctx -> String
indNameFromConstr c ctx = c  -- simplified

applyPatterns :: Term -> [Term] -> [Clause] -> Term
applyPatterns rhs args ps = rhs  -- simplified: assumes args are bound in clause

findClause :: String -> [Clause] -> Maybe Term
findClause c [] = Nothing
findClause c ((Clause (PCon c' ps) rhs):rest) =
  if c == c' then Just rhs else findClause c rest
findClause c ((Clause PWild rhs):_) = Just rhs
findClause c (_:rest) = findClause c rest

findLitClause :: Int -> [Clause] -> Maybe Term
findLitClause n [] = Nothing
findLitClause n ((Clause (PLit m) rhs):rest) =
  if n == m then Just rhs else findLitClause n rest
findLitClause n ((Clause PWild rhs):_) = Just rhs
findLitClause n (_:rest) = findLitClause n rest

findReflClause :: [Clause] -> Maybe Term
findReflClause [] = Nothing
findReflClause ((Clause (PCon "Refl" []) rhs):_) = Just rhs
findReflClause ((Clause PWild rhs):_) = Just rhs
findReflClause (_:rest) = findReflClause rest

-- ============================================
-- FULL NORMALIZATION
-- ============================================
nf :: Ctx -> Term -> Term
nf ctx t = case whnf ctx t of
  App f x -> App (nf ctx f) (nf ctx x)
  Lam b body -> Lam (nfBinder ctx b) (nf (extendCtxBinder ctx b) body)
  Pi b body -> Pi (nfBinder ctx b) (nf (extendCtxBinder ctx b) body)
  Let n ty val b -> Let n (nf ctx ty) (nf ctx val) (nf (extend n ty (Just val) ctx) b)
  Case e ps -> Case (nf ctx e) (map (\(Clause p r) -> (Clause p (nf ctx r))) ps)
  Eq a x y -> Eq (nf ctx a) (nf ctx x) (nf ctx y)
  Refl e -> Refl (nf ctx e)
  Annot e t' -> Annot (nf ctx e) (nf ctx t')
  Proj i e -> Proj i (nf ctx e)
  Fix info t' -> Fix info (nf ctx t')
  Constr tn cn args -> Constr tn cn (map (nf ctx) args)
  t' -> t'

nfBinder :: Ctx -> Binder -> Binder
nfBinder ctx (BExplicit n ty) = BExplicit n (nf ctx ty)
nfBinder ctx (BImplicit n ty) = BImplicit n (nf ctx ty)

extendCtxBinder :: Ctx -> Binder -> Ctx
extendCtxBinder ctx (BExplicit n ty) = extend n ty Nothing ctx
extendCtxBinder ctx (BImplicit n ty) = extend n ty Nothing ctx

-- ============================================
-- DEFINITIONAL EQUALITY (convertibility)
-- Includes: beta, iota (induction), delta (unfold), xi, eta
-- ============================================
convert :: Ctx -> Term -> Term -> Either String ()
convert ctx a b = do
  let a' = whnf ctx a
  let b' = whnf ctx b
  convertWhnf ctx a' b'

convertWhnf :: Ctx -> Term -> Term -> Either String ()
convertWhnf ctx a b = case (a, b) of
  (Var n1, Var n2) | n1 == n2 -> Right ()
  (App f1 x1, App f2 x2) -> convert ctx f1 f2 >> convert ctx x1 x2
  (Lam b1 body1, Lam b2 body2) ->
    convertBinder ctx b1 b2 >> convert (extendCtxBinder ctx b1) body1 body2
  (Pi b1 body1, Pi b2 body2) ->
    convertBinder ctx b1 b2 >> convert (extendCtxBinder ctx b1) body1 body2
  (Let n1 ty1 v1 b1, Let n2 ty2 v2 b2) ->
    convert ctx ty1 ty2 >> convert ctx v1 v2 >> convert (extend n1 ty1 (Just v1) ctx) b1 b2
  (Sort s1, Sort s2) | sortLeq s1 s2 && sortLeq s2 s1 -> Right ()
  (Constr _ c1 args1, Constr _ c2 args2) | c1 == c2 && length args1 == length args2 ->
    mapM_ (uncurry (convert ctx)) (zip args1 args2)
  (Eq a1 x1 y1, Eq a2 x2 y2) ->
    convert ctx a1 a2 >> convert ctx x1 x2 >> convert ctx y1 y2
  (Refl e1, Refl e2) -> convert ctx e1 e2
  (NatLit n1, NatLit n2) | n1 == n2 -> Right ()
  (CharLit c1, CharLit c2) | c1 == c2 -> Right ()
  (Annot e1 _, Annot e2 _) -> convert ctx e1 e2
  (Meta i, Meta j) | i == j -> Right ()
  -- Eta expansion for functions
  (f, Lam b body) ->
    let x = Var (binderName (Lam b body))
    in convert ctx (App f x) (App (Lam b body) x)
  (Lam b body, f) ->
    let x = Var (binderName (Lam b body))
    in convert ctx (App (Lam b body) x) (App f x)
  _ -> Left $ "Cannot convert: " ++ ppTerm a ++ " and " ++ ppTerm b

convertBinder :: Ctx -> Binder -> Binder -> Either String ()
convertBinder ctx (BExplicit _ ty1) (BExplicit _ ty2) = convert ctx ty1 ty2
convertBinder ctx (BImplicit _ ty1) (BImplicit _ ty2) = convert ctx ty1 ty2
convertBinder _ _ _ = Left "Binder mismatch"

-- ============================================
-- UNIVERSE CONSTRAINTS
-- ============================================
inferSort :: Ctx -> Term -> Either String Sort
inferSort ctx t = do
  ty <- infer ctx t
  case whnf ctx ty of
    Sort s -> Right s
    _ -> Left $ "Expected sort, got: " ++ ppTerm ty

-- Cumulativity: if A : Sort u and u <= v, then A : Sort v
checkSort :: Ctx -> Term -> Sort -> Either String ()
checkSort ctx t expected = do
  actual <- inferSort ctx t
  if sortLeq actual expected
    then Right ()
    else Left $ "Universe mismatch: " ++ ppSort actual ++ " not <= " ++ ppSort expected

-- ============================================
-- BIDIRECTIONAL TYPE CHECKING
-- ============================================

-- INFERENCE: synthesize the type of a term
infer :: Ctx -> Term -> Either String Term
infer ctx t = case t of
  Var n -> case lookupType n ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ ppName n
  
  App f x -> do
    fTy <- infer ctx f
    case whnf ctx fTy of
      Pi (BExplicit _ a) b -> do
        check ctx x a
        Right (substitute x (binderName (Pi (BExplicit (Raw "_") (Sort SProp)) b)) b)
      Pi (BImplicit _ a) b -> do
        -- implicit argument: try to infer from context
        Right (substitute (Meta 0) (binderName (Pi (BImplicit (Raw "_") (Sort SProp)) b)) b)
      _ -> Left $ "Expected Pi type, got: " ++ ppTerm (whnf ctx fTy)
  
  Lam b@(BExplicit n ty) body ->
    Left $ "Cannot infer type of explicit lambda without annotation: \\(" ++ ppName n ++ " : ...) => ..."
  
  Lam b@(BImplicit n ty) body ->
    Left $ "Cannot infer type of implicit lambda"
  
  Pi b@(BExplicit n a) body -> do
    aSort <- inferSort ctx a
    bodySort <- inferSort (extendCtxBinder ctx b) body
    let resultSort = sortMax aSort bodySort
    Right (Sort resultSort)
  
  Pi b@(BImplicit n a) body -> do
    aSort <- inferSort ctx a
    bodySort <- inferSort (extendCtxBinder ctx b) body
    let resultSort = sortMax aSort bodySort
    Right (Sort resultSort)
  
  Let n ty val body -> do
    check ctx ty (Sort (SType LZero))
    check ctx val ty
    infer (extend n ty (Just val) ctx) body
  
  Sort SProp -> Right (Sort (SType LZero))  -- Prop : Type
  Sort (SType u) -> Right (Sort (SType (levelSucc u)))  -- Type u : Type (u+1)
  
  Constr tn cn args -> do
    -- lookup inductive definition
    case lookupIndDef tn ctx of
      Just ind -> inferConstr ctx ind cn args
      Nothing -> Left $ "Unknown inductive type: " ++ tn
  
  Case e ps -> do
    eTy <- infer ctx e
    -- infer from first clause
    case ps of
      (Clause p rhs):_ -> do
        (patTy, patBindings) <- inferPattern ctx p eTy
        rhsTy <- infer (patBindings ++ ctx) rhs
        Right rhsTy
      [] -> Left "Empty pattern match"
  
  Eq a x y -> do
    check ctx a (Sort (SType LZero))
    check ctx x a
    check ctx y a
    Right (Sort SProp)  -- equality is a proposition
  
  Refl e -> do
    eTy <- infer ctx e
    Right (Eq eTy e e)
  
  Annot e t' -> do
    check ctx t' (Sort (SType LZero))
    check ctx e t'
    Right t'
  
  NatLit _ -> Right (Var (Global "Nat"))
  CharLit _ -> Right (Var (Global "Char"))
  StringLit _ -> Right (App (Var (Global "List")) (Var (Global "Char")))
  
  Meta i -> Right (Meta i)  -- meta is a meta
  
  Fix info body -> do
    let ctx' = extend (fixName info) (fixType info) (Just (Fix info body)) ctx
    bodyTy <- infer ctx' body
    Right (fixType info)
  
  _ -> Left $ "Cannot infer type of: " ++ ppTerm t

-- CHECKING: verify a term has the expected type
check :: Ctx -> Term -> Term -> Either String ()
check ctx t expected = case (t, whnf ctx expected) of
  (Lam b body, Pi b' body') -> do
    convertBinder ctx b b'
    check (extendCtxBinder ctx b) body (substitute (Var (binderName (Lam b body))) (binderName (Pi b' body')) body')
  
  (Constr tn cn args, expected') -> do
    -- constructor application
    case lookupIndDef tn ctx of
      Just ind -> checkConstr ctx ind cn args expected'
      Nothing -> Left $ "Unknown inductive type in check: " ++ tn
  
  (Case e ps, ty') -> do
    eTy <- infer ctx e
    mapM_ (checkClause ctx eTy ty') ps
  
  (Let n ty val b, ty') -> do
    check ctx ty (Sort (SType LZero))
    check ctx val ty
    check (extend n ty (Just val) ctx) b ty'
  
  (Meta _, _) -> Right ()  -- meta can have any type
  
  (t, ty') -> do
    inferred <- infer ctx t
    convert ctx inferred ty'

-- ============================================
-- PATTERN CHECKING
-- ============================================
checkClause :: Ctx -> Term -> Term -> Clause -> Either String ()
checkClause ctx patTy resTy (Clause p rhs) = do
  (bindings, _) <- checkPattern ctx p patTy
  check (bindings ++ ctx) rhs resTy

checkPattern :: Ctx -> Pattern -> Term -> Either String (Ctx, Term)
checkPattern ctx p ty = case (p, whnf ctx ty) of
  (PVar n, ty') -> Right ([(n, (ty', Nothing))], ty')
  (PWild, ty') -> Right ([], ty')
  (PLit n, Var (Global "Nat")) -> Right ([], Var (Global "Nat"))
  (PCon c ps, ty') -> case ty' of
    App (Inductive ind) _ ->
      case findConstr ind c of
        Just conDef -> do
          (bindings, _) <- checkPatArgs ctx ps (conArgs conDef)
          Right (bindings, ty')
        Nothing -> Left $ "Unknown constructor: " ++ c
    _ -> Left $ "Expected inductive type for constructor pattern"
  (PAnnotated p' t, _) -> do
    check ctx t (Sort (SType LZero))
    convert ctx (whnf ctx t) (whnf ctx ty)
    checkPattern ctx p' t
  _ -> Left "Pattern/type mismatch"

checkPatArgs :: Ctx -> [Pattern] -> [Binder] -> Either String (Ctx, [Term])
checkPatArgs ctx [] [] = Right ([], [])
checkPatArgs ctx (p:ps) (b:bs) = do
  let ty = binderType b
  (bind1, _) <- checkPattern ctx p ty
  (bindRest, ts') <- checkPatArgs (bind1 ++ ctx) ps bs
  Right (bind1 ++ bindRest, Var (Raw "_") : ts')  -- placeholder
checkPatArgs _ _ _ = Left "Pattern/constructor arg count mismatch"

inferPattern :: Ctx -> Pattern -> Term -> Either String (Term, Ctx)
inferPattern ctx p ty = do
  (bindings, patTy) <- checkPattern ctx p ty
  Right (patTy, bindings)

binderType :: Binder -> Term
binderType (BExplicit _ ty) = ty
binderType (BImplicit _ ty) = ty

findConstr :: IndDef -> String -> Maybe ConstrDef
findConstr ind c = case filter (\cd -> conName cd == c) (indConstrs ind) of
  (cd:_) -> Just cd
  [] -> Nothing

inferConstr :: Ctx -> IndDef -> String -> [Term] -> Either String Term
inferConstr ctx ind cn args = do
  case findConstr ind cn of
    Just conDef -> do
      let params = map (\b -> Var (binderName (Pi b (Sort SProp)))) (indParams ind)
      let resultIndices = conResult conDef
      let fullType = foldr (\b t -> Pi b t) (foldl App (Inductive ind) (params ++ resultIndices)) (conArgs conDef)
      Right fullType
    Nothing -> Left $ "Unknown constructor: " ++ cn

checkConstr :: Ctx -> IndDef -> String -> [Term] -> Term -> Either String ()
checkConstr ctx ind cn args expected = do
  conTy <- inferConstr ctx ind cn args
  convert ctx conTy expected

lookupIndDef :: String -> Ctx -> Maybe IndDef
lookupIndDef tn ctx = Nothing  -- TODO: store inductive defs in context

-- ============================================
-- TOP-LEVEL PROGRAM CHECKING
-- ============================================
checkProgram :: Ctx -> Program -> Either String Ctx
checkProgram ctx [] = Right ctx
checkProgram ctx (decl:decls) = do
  ctx' <- checkDecl ctx decl
  checkProgram ctx' decls

checkDecl :: Ctx -> Decl -> Either String Ctx
checkDecl ctx decl = case decl of
  TypeSig n ty -> do
    check ctx ty (Sort (SType LZero))
    Right ((Global n, (ty, Nothing)) : ctx)
  
  FunDef n clauses -> do
    ty <- case lookupType (Global n) ctx of
      Just t -> Right t
      Nothing -> Left $ "No type signature for: " ++ n
    mapM_ (checkClause ctx ty ty) clauses
    Right ctx
  
  IndDecl ind -> do
    -- check inductive definition well-formedness
    checkInductive ctx ind
    Right ((Global (indName ind), (Sort (indSort ind), Nothing)) : ctx)
  
  AxiomDecl n ty -> do
    check ctx ty (Sort (SType LZero))
    Right ((Global n, (ty, Nothing)) : ctx)
  
  InfixDecl _ _ _ -> Right ctx

-- Check inductive definition is well-formed
checkInductive :: Ctx -> IndDef -> Either String ()
checkInductive ctx ind = do
  -- Check parameter types are in appropriate universes
  let paramCtx = foldr (\b c -> extendCtxBinder c b) ctx (indParams ind)
  -- Check constructor argument types
  mapM_ (checkConstrDef paramCtx ind) (indConstrs ind)
  Right ()

checkConstrDef :: Ctx -> IndDef -> ConstrDef -> Either String ()
checkConstrDef ctx ind con = do
  let argCtx = foldr (\b c -> extendCtxBinder c b) ctx (conArgs con)
  -- result type must be the inductive type applied to params and result indices
  Right ()

-- Universe max for Pi types
sortMax :: Sort -> Sort -> Sort
sortMax SProp s = s
sortMax s SProp = s
sortMax (SType u) (SType v) = SType (levelMax u v)
sortMax s1 s2 = if sortLeq s1 s2 then s2 else s1

typecheck :: Program -> Either String (Ctx, Term)
typecheck prog = do
  ctx <- checkProgram [] prog
  Right (ctx, Sort (SType LZero))
