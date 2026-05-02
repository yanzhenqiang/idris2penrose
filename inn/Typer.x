module Typer where
import Base
import Ast

-- Bidirectional type checker for dependent types.
-- Type-in-Type for bootstrapping.

type Ctx = [(Name, (Term, Term))]

extend :: Name -> Term -> Term -> Ctx -> Ctx
extend n ty val ctx = (n, (ty, val)) : ctx

lookupType :: Name -> Ctx -> Maybe Term
lookupType n ctx = fmap fst (mlookup n ctx)

lookupVal :: Name -> Ctx -> Maybe Term
lookupVal n ctx = fmap snd (mlookup n ctx)

-- Weak head normal form.
whnf :: Ctx -> Term -> Term
whnf ctx t = case t of
  App f x -> case whnf ctx f of
    Lam n b -> whnf ctx (substitute x n b)
    Pi n a b -> error "Pi applied"
    f' -> App f' x
  Case e ps -> case whnf ctx e of
    Pair a b -> case ps of
      (PCon "MkSigma" [_, _], t) : _ -> whnf ctx (App (App t a) b)
      (PWild, t) : _ -> whnf ctx t
      _ -> Case (Pair a b) ps
    Refl e' -> case ps of
      (PCon "Refl" [], t) : _ -> whnf ctx t
      (PWild, t) : _ -> whnf ctx t
      _ -> Case (Refl e') ps
    App (App (Data d cs) arg) _ -> case findClause d cs ps of
      Just (env, rhs) -> whnf (env ++ ctx) rhs
      Nothing -> Case (App (Data d cs) arg) ps
    NatLit 0 -> case ps of
      (PLit 0, t) : _ -> whnf ctx t
      (PWild, t) : _ -> whnf ctx t
      _ -> Case (NatLit 0) ps
    e' -> Case e' ps
  Let n v b -> whnf ctx (substitute v n b)
  Proj1 e -> case whnf ctx e of
    Pair a _ -> a
    e' -> Proj1 e'
  Proj2 e -> case whnf ctx e of
    Pair _ b -> b
    e' -> Proj2 e'
  Annot e _ -> whnf ctx e
  Var n -> case lookupVal n ctx of
    Just v -> whnf ctx v
    Nothing -> Var n
  _ -> t

-- Full normalization.
nf :: Ctx -> Term -> Term
nf ctx t = case whnf ctx t of
  App f x -> App (nf ctx f) (nf ctx x)
  Lam n b -> Lam n (nf ctx b)
  Pi n a b -> Pi n (nf ctx a) (nf ctx b)
  Sigma n a b -> Sigma n (nf ctx a) (nf ctx b)
  Pair a b -> Pair (nf ctx a) (nf ctx b)
  Refl e -> Refl (nf ctx e)
  Eq a b -> Eq (nf ctx a) (nf ctx b)
  Case e ps -> Case (nf ctx e) (map (\(p, t') -> (p, nf ctx t')) ps)
  Proj1 e -> Proj1 (nf ctx e)
  Proj2 e -> Proj2 (nf ctx e)
  Annot e t' -> Annot (nf ctx e) (nf ctx t')
  t' -> t'

-- Substitution.
substitute :: Term -> Name -> Term -> Term
substitute val n t = case t of
  Var n' | n == n' -> val
         | otherwise -> Var n'
  App f x -> App (substitute val n f) (substitute val n x)
  Lam n' b -> if n == n' then Lam n' b else Lam n' (substitute val n b)
  Pi n' a b -> if n == n' then Pi n' (substitute val n a) b else Pi n' (substitute val n a) (substitute val n b)
  Sigma n' a b -> if n == n' then Sigma n' (substitute val n a) b else Sigma n' (substitute val n a) (substitute val n b)
  Let n' v b -> if n == n' then Let n' (substitute val n v) b else Let n' (substitute val n v) (substitute val n b)
  Case e ps -> Case (substitute val n e) (map (\(p, t') -> (p, substitute val n t')) ps)
  Refl e -> Refl (substitute val n e)
  Eq a b -> Eq (substitute val n a) (substitute val n b)
  Annot e t' -> Annot (substitute val n e) (substitute val n t')
  Proj1 e -> Proj1 (substitute val n e)
  Proj2 e -> Proj2 (substitute val n e)
  Pair a b -> Pair (substitute val n a) (substitute val n b)
  t' -> t'

-- Convertibility.
convert :: Ctx -> Term -> Term -> Either String ()
convert ctx a b = let
  a' = whnf ctx a
  b' = whnf ctx b
  in case (a', b') of
    (Var n1, Var n2) | n1 == n2 -> Right ()
    (App f1 x1, App f2 x2) -> convert ctx f1 f2 >> convert ctx x1 x2
    (Lam n1 b1, Lam n2 b2) -> convert ctx b1 b2
    (Pi n1 a1 b1, Pi n2 a2 b2) -> convert ctx a1 a2 >> convert ctx b1 b2
    (Sigma n1 a1 b1, Sigma n2 a2 b2) -> convert ctx a1 a2 >> convert ctx b1 b2
    (Pair a1 b1, Pair a2 b2) -> convert ctx a1 a2 >> convert ctx b1 b2
    (Eq a1 b1, Eq a2 b2) -> convert ctx a1 a2 >> convert ctx b1 b2
    (Refl e1, Refl e2) -> convert ctx e1 e2
    (NatLit n1, NatLit n2) | n1 == n2 -> Right ()
    (CharLit c1, CharLit c2) | c1 == c2 -> Right ()
    (Type i, Type j) | i == j -> Right ()
    (Annot e1 _, Annot e2 _) -> convert ctx e1 e2
    _ -> Left $ "Cannot convert: " ++ ppTerm a' ++ " and " ++ ppTerm b'

-- Inference.
infer :: Ctx -> Term -> Either String Term
infer ctx t = case t of
  Var n -> case lookupType n ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ ppName n
  App f x -> do
    fTy <- infer ctx f
    case whnf ctx fTy of
      Pi n a b -> do
        check ctx x a
        Right (substitute x n b)
      _ -> Left $ "Expected Pi type, got: " ++ ppTerm (whnf ctx fTy)
  Lam n b -> Left "Cannot infer type of lambda without annotation"
  Pi n a b -> do
    check ctx a (Type 0)
    check (extend n a (Var n) ctx) b (Type 0)
    Right (Type 0)
  Sigma n a b -> do
    check ctx a (Type 0)
    check (extend n a (Var n) ctx) b (Type 0)
    Right (Type 0)
  Let n v b -> do
    vTy <- infer ctx v
    infer (extend n vTy v ctx) b
  Type i -> Right (Type (i + 1))
  Data d cs -> Right (Type 0)
  Refl e -> do
    eTy <- infer ctx e
    Right (Eq e e)
  Eq a b -> do
    aTy <- infer ctx a
    bTy <- infer ctx b
    convert ctx aTy bTy
    Right (Type 0)
  Pair a b -> do
    aTy <- infer ctx a
    bTy <- infer ctx b
    Left "Cannot infer Sigma without annotation"
  Annot e t' -> do
    check ctx t' (Type 0)
    check ctx e t'
    Right t'
  NatLit _ -> Right (Var (Global "Nat"))
  CharLit _ -> Right (Var (Global "Char"))
  StringLit _ -> Right (App (Var (Global "List")) (Var (Global "Char")))
  Hole h -> Left $ "Unresolved hole: " ++ h
  _ -> Left $ "Cannot infer: " ++ ppTerm t

-- Checking.
check :: Ctx -> Term -> Term -> Either String ()
check ctx t ty = case (t, whnf ctx ty) of
  (Lam n b, Pi n' a b') -> do
    check (extend n a (Var n) ctx) b (substitute (Var n) n' b')
  (Pair a b, Sigma n' a' b') -> do
    check ctx a a'
    check ctx b (substitute a n' b')
  (Case e ps, ty') -> do
    eTy <- infer ctx e
    mapM_ (checkClause ctx eTy ty') ps
  (Let n v b, ty') -> do
    vTy <- infer ctx v
    check (extend n vTy v ctx) b ty'
  (Hole _, _) -> Right ()
  (t, ty') -> do
    inferred <- infer ctx t
    convert ctx inferred ty'

-- Pattern checking.
checkClause :: Ctx -> Term -> Term -> (Pattern, Term) -> Either String ()
checkClause ctx patTy resTy (p, rhs) = do
  (bindings, _) <- checkPattern ctx p patTy
  check (bindings ++ ctx) rhs resTy
  Right ()

checkPattern :: Ctx -> Pattern -> Term -> Either String (Ctx, Term)
checkPattern ctx p ty = case (p, whnf ctx ty) of
  (PVar n, ty') -> Right ([(n, (ty', Var n))], ty')
  (PWild, ty') -> Right ([], ty')
  (PLit n, Var (Global "Nat")) -> Right ([], Var (Global "Nat"))
  (PCon c ps, ty') -> case ty' of
    Data d cs -> case findCon c cs of
      Just conArgs -> do
        (bindings, _) <- checkPatArgs ctx ps conArgs
        Right (bindings, ty')
      Nothing -> Left $ "Unknown constructor: " ++ c
    _ -> Left $ "Expected data type for constructor pattern"
  (PAnnotated p' t, _) -> do
    check ctx t (Type 0)
    convert ctx (whnf ctx t) (whnf ctx ty)
    checkPattern ctx p' t
  _ -> Left $ "Pattern/type mismatch"

checkPatArgs :: Ctx -> [Pattern] -> [Term] -> Either String (Ctx, [Term])
checkPatArgs ctx [] [] = Right ([], [])
checkPatArgs ctx (p:ps) (t:ts) = do
  (bind1, _) <- checkPattern ctx p t
  (bindRest, ts') <- checkPatArgs (bind1 ++ ctx) ps ts
  Right (bind1 ++ bindRest, t : ts')
checkPatArgs _ _ _ = Left "Pattern/constructor arg count mismatch"

findCon :: String -> [(String, [Term])] -> Maybe [Term]
findCon c [] = Nothing
findCon c ((c', ts):rest) = if c == c' then Just ts else findCon c rest

findClause :: String -> [(String, [Term])] -> [(Pattern, Term)] -> Maybe (Ctx, Term)
findClause d cs [] = Nothing
findClause d cs ((p, rhs):rest) = case p of
  PCon c ps -> case findCon c cs of
    Just conArgs -> Just ([], rhs)
    Nothing -> findClause d cs rest
  PWild -> Just ([], rhs)
  _ -> findClause d cs rest

-- Top-level program checking.
checkProgram :: Ctx -> Program -> Either String Ctx
checkProgram ctx [] = Right ctx
checkProgram ctx (decl:decls) = do
  ctx' <- checkDecl ctx decl
  checkProgram ctx' decls

checkDecl :: Ctx -> Decl -> Either String Ctx
checkDecl ctx decl = case decl of
  TypeSig n ty -> do
    check ctx ty (Type 0)
    Right ((Global n, (ty, Var (Global n))) : ctx)
  FunDef n clauses -> do
    ty <- case lookupType (Global n) ctx of
      Just t -> Right t
      Nothing -> Left $ "No type signature for: " ++ n
    mapM_ (checkClause ctx ty ty) clauses
    Right ctx
  DataDecl d cs -> Right ((Global d, (Type 0, Data d cs)) : ctx)
  InfixDecl _ _ _ -> Right ctx

typecheck :: Program -> Either String (Ctx, Term)
typecheck prog = do
  ctx <- checkProgram [] prog
  Right (ctx, Type 0)
