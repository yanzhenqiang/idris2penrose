module Ast where
import Base

-- Abstract syntax for a dependently typed language (.x).
-- Types are terms: Type-in-Type for bootstrapping.

data Name = Raw String | Ind Int | Global String deriving (Eq, Show)

-- Terms: expressions and types unified.
data Term
  = Var Name
  | App Term Term
  | Lam Name Term
  | Pi Name Term Term        -- (x : A) -> B
  | Sigma Name Term Term     -- (x : A ** B)
  | Let Name Term Term       -- let x = v in t
  | Type Int                 -- Type i (universe level)
  | Data String [(String, [Term])]  -- data D = C1 T1 | C2 T2 | ...
  | Case Term [(Pattern, Term)]
  | Refl Term                -- Refl : x = x
  | Eq Term Term             -- x = y
  | Annot Term Term          -- e : T
  | Proj1 Term               -- fst
  | Proj2 Term               -- snd
  | Pair Term Term           -- (a, b)
  | Hole String              -- ?hole
  | NatLit Int
  | CharLit Int
  | StringLit String
  deriving (Eq, Show)

-- Patterns.
data Pattern
  = PVar Name
  | PCon String [Pattern]
  | PLit Int
  | PWild
  | PAnnotated Pattern Term
  deriving (Eq, Show)

-- Declarations.
data Decl
  = TypeSig String Term
  | FunDef String [Clause]
  | DataDecl String [(String, [Term])]
  | InfixDecl Fixity Int [String]
  deriving (Eq, Show)

data Fixity = Infix | InfixL | InfixR deriving (Eq, Show)

data Clause = Clause [Pattern] Term deriving (Eq, Show)

type Program = [Decl]

-- Pretty printing.
ppName (Raw s) = s
ppName (Ind i) = show i
ppName (Global s) = s

ppTerm (Var n) = ppName n
ppTerm (App f x) = "(" ++ ppTerm f ++ " " ++ ppTerm x ++ ")"
ppTerm (Lam n b) = "\\" ++ ppName n ++ " -> " ++ ppTerm b
ppTerm (Pi n a b)
  | n == Raw "_" = "(" ++ ppTerm a ++ " -> " ++ ppTerm b ++ ")"
  | otherwise = "(" ++ ppName n ++ " : " ++ ppTerm a ++ ") -> " ++ ppTerm b
ppTerm (Sigma n a b)
  | n == Raw "_" = "(" ++ ppTerm a ++ " ** " ++ ppTerm b ++ ")"
  | otherwise = "(" ++ ppName n ++ " : " ++ ppTerm a ++ ") ** " ++ ppTerm b
ppTerm (Let n v b) = "let " ++ ppName n ++ " = " ++ ppTerm v ++ " in " ++ ppTerm b
ppTerm (Type i) = "Type" ++ if i == 0 then "" else show i
ppTerm (Data n cs) = "data " ++ n ++ " = " ++ intercalate " | " (map (\(c, ts) -> c ++ " " ++ unwords (map ppTerm ts)) cs)
ppTerm (Case e ps) = "case " ++ ppTerm e ++ " of { " ++ intercalate " ; " (map (\(p, t) -> ppPat p ++ " => " ++ ppTerm t) ps) ++ " }"
ppTerm (Refl e) = "Refl " ++ ppTerm e
ppTerm (Eq a b) = "(" ++ ppTerm a ++ " = " ++ ppTerm b ++ ")"
ppTerm (Annot e t) = "(" ++ ppTerm e ++ " : " ++ ppTerm t ++ ")"
ppTerm (Proj1 e) = "fst " ++ ppTerm e
ppTerm (Proj2 e) = "snd " ++ ppTerm e
ppTerm (Pair a b) = "(" ++ ppTerm a ++ ", " ++ ppTerm b ++ ")"
ppTerm (Hole h) = "?" ++ h
ppTerm (NatLit n) = show n
ppTerm (CharLit c) = "'" ++ chr c : "'"
ppTerm (StringLit s) = "\"" ++ s ++ "\""

ppPat (PVar n) = ppName n
ppPat (PCon c ps) = "(" ++ c ++ " " ++ unwords (map ppPat ps) ++ ")"
ppPat (PLit n) = show n
ppPat PWild = "_"
ppPat (PAnnotated p t) = "(" ++ ppPat p ++ " : " ++ ppTerm t ++ ")"

-- De Bruijn conversion.
toDeBruijn :: [(Name, Int)] -> Term -> Term
toDeBruijn env t = case t of
  Var n -> case lookup n env of
    Just i -> Var (Ind i)
    Nothing -> Var n
  App f x -> App (toDeBruijn env f) (toDeBruijn env x)
  Lam n b -> Lam (Ind 0) (toDeBruijn ((n, 0) : map (second (+1)) env) (shift 1 b))
  Pi n a b -> Pi (Ind 0) (toDeBruijn env a) (toDeBruijn ((n, 0) : map (second (+1)) env) (shift 1 b))
  Sigma n a b -> Sigma (Ind 0) (toDeBruijn env a) (toDeBruijn ((n, 0) : map (second (+1)) env) (shift 1 b))
  Let n v b -> Let (Ind 0) (toDeBruijn env v) (toDeBruijn ((n, 0) : map (second (+1)) env) (shift 1 b))
  Case e ps -> Case (toDeBruijn env e) (map (\(p, t) -> (toDBPat p, toDeBruijn (patEnv p env) t)) ps)
  Refl e -> Refl (toDeBruijn env e)
  Eq a b -> Eq (toDeBruijn env a) (toDeBruijn env b)
  Annot e t' -> Annot (toDeBruijn env e) (toDeBruijn env t')
  Proj1 e -> Proj1 (toDeBruijn env e)
  Proj2 e -> Proj2 (toDeBruijn env e)
  Pair a b -> Pair (toDeBruijn env a) (toDeBruijn env b)
  _ -> t

shift k t = case t of
  Var (Ind i) -> Var (Ind $ if i < k then i else i + 1)
  Var n -> Var n
  App f x -> App (shift k f) (shift k x)
  Lam n b -> Lam n (shift (k+1) b)
  Pi n a b -> Pi n (shift k a) (shift (k+1) b)
  Sigma n a b -> Sigma n (shift k a) (shift (k+1) b)
  Let n v b -> Let n (shift k v) (shift (k+1) b)
  Case e ps -> Case (shift k e) (map (\(p, t) -> (shiftPat k p, shift k t)) ps)
  Refl e -> Refl (shift k e)
  Eq a b -> Eq (shift k a) (shift k b)
  Annot e t' -> Annot (shift k e) (shift k t')
  Proj1 e -> Proj1 (shift k e)
  Proj2 e -> Proj2 (shift k e)
  Pair a b -> Pair (shift k a) (shift k b)
  _ -> t

toDBPat p = case p of
  PVar n -> PVar (Ind 0)
  PCon c ps -> PCon c (map toDBPat ps)
  PLit n -> PLit n
  PWild -> PWild
  PAnnotated p' t -> PAnnotated (toDBPat p') (shift (patDepth p') t)

patEnv p env = case p of
  PVar n -> (n, 0) : map (second (+1)) env
  PCon _ ps -> foldr (\p' e -> patEnv p' e) env ps
  PLit _ -> env
  PWild -> env
  PAnnotated p' _ -> patEnv p' env

patDepth p = case p of
  PVar _ -> 1
  PCon _ ps -> sum (map patDepth ps)
  PLit _ -> 0
  PWild -> 0
  PAnnotated p' _ -> patDepth p'

shiftPat k p = case p of
  PVar n -> PVar (Ind $ case n of Ind i -> if i < k then i else i + 1; _ -> 0)
  PCon c ps -> PCon c (map (shiftPat k) ps)
  _ -> p
