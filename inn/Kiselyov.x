module Kiselyov where
import Base
import Ast

-- Type erasure + Kiselyov optimal bracket abstraction.
-- Dependent types are completely erased.

data LamTerm = LVar Name | LApp LamTerm LamTerm | LLam Name LamTerm | LCon String | LPrim String

erase :: Term -> LamTerm
erase t = case t of
  Var n -> LVar n
  App f x -> LApp (erase f) (erase x)
  Lam n b -> LLam n (erase b)
  Pi _ _ b -> erase b
  Sigma _ _ b -> erase b
  Let n v b -> LApp (LLam n (erase b)) (erase v)
  Data d _ -> LCon d
  Case e ps -> foldl LApp (LCon "case") (erase e : map (\(p, t) -> LApp (erasePat p) (erase t)) ps)
  Refl e -> erase e
  Eq a b -> erase a
  Pair a b -> LApp (LApp (LCon "MkSigma") (erase a)) (erase b)
  Annot e _ -> erase e
  NatLit n -> LPrim (show n)
  CharLit c -> LPrim ("chr" ++ show c)
  StringLit s -> LPrim ("str" ++ s)
  Proj1 e -> LApp (LPrim "fst") (erase e)
  Proj2 e -> LApp (LPrim "snd") (erase e)
  _ -> LVar (Raw "undefined")

erasePat p = case p of
  PVar n -> LVar n
  PCon c ps -> foldl LApp (LCon c) (map erasePat ps)
  PLit n -> LPrim (show n)
  PWild -> LVar (Raw "_")
  PAnnotated p' _ -> erasePat p'

abstract :: Name -> LamTerm -> LamTerm
abstract n t = case t of
  LVar n' | n == n' -> LPrim "I"
          | otherwise -> LApp (LPrim "K") (LVar n')
  LApp f x -> case (isFree n f, isFree n x) of
    (False, False) -> LApp (LPrim "K") (LApp f x)
    (True, False) -> LApp (LApp (LPrim "B") (abstract n f)) x
    (False, True) -> LApp (LApp (LPrim "C") f) (abstract n x)
    (True, True) -> LApp (LApp (LPrim "S") (abstract n f)) (abstract n x)
  LLam n' b | n == n' -> t
            | otherwise -> abstract n (LLam n' (abstract n b))
  LCon c -> LApp (LPrim "K") (LCon c)
  LPrim s -> LApp (LPrim "K") (LPrim s)

isFree n t = case t of
  LVar n' -> n == n'
  LApp f x -> isFree n f || isFree n x
  LLam n' b -> n /= n' && isFree n b
  _ -> False

compile :: LamTerm -> String
compile t = case t of
  LVar (Raw s) -> s
  LVar (Global s) -> s
  LVar (Ind i) -> "v" ++ show i
  LApp f x -> "(" ++ compile f ++ " " ++ compile x ++ ")"
  LLam n b -> compile (abstract n b)
  LCon c -> c
  LPrim s -> s

compileTerm :: Term -> String
compileTerm = compile . erase

compileDecl :: Decl -> String
compileDecl decl = case decl of
  TypeSig _ _ -> ""
  FunDef n cs -> compileClauses n cs
  DataDecl d cs -> ""
  InfixDecl _ _ _ -> ""

compileClauses :: String -> [Clause] -> String
compileClauses n cs = n ++ " = " ++ case cs of
  [Clause [] rhs] -> compileTerm rhs
  _ -> foldr (\c acc -> compileClause n c acc) (LPrim "undefined") cs

compileClause :: String -> Clause -> String -> String
compileClause n (Clause ps rhs) fallback = "case " ++ n ++ " of { " ++ intercalate " ; " (map (\p -> ppPat p ++ " => " ++ compileTerm rhs) ps) ++ " ; _ => " ++ fallback ++ " }"

compileProgram :: Program -> String
compileProgram prog = unlines $ filter (not . null) $ map compileDecl prog
