module Ast where
import Base

-- ============================================
-- CIC AST (Calculus of Inductive Constructions)
-- Based on Lean 4 / Coq core type theory
-- ============================================

-- Universe levels: natural numbers with arithmetic
data Level
  = LZero          -- 0
  | LSucc Level    -- u + 1
  | LMax Level Level
  | LVar String    -- universe polymorphism variable
  deriving (Eq, Show)

-- Sort: the typing universes
data Sort
  = SProp          -- Sort 0: proof-irrelevant propositions
  | SType Level    -- Sort (u+1): Type u
  | SSucc Sort     -- successor universe (for cumulativity)
  deriving (Eq, Show)

-- Names: raw, De Bruijn index, or global
data Name = Raw String | Ind Int | Global String deriving (Eq, Show)

-- ============================================
-- TERMS: Core CIC syntax
-- ============================================
data Term
  = Var Name                     -- variable
  | App Term Term                -- application f x
  | Lam Binder Term              -- lambda
  | Pi Binder Term               -- dependent function type
  | Let Name Term Term Term      -- let x : T = v in b
  | Sort Sort                    -- universe sort
  | Inductive IndDef             -- inductive type definition
  | Constr String String [Term]  -- constructor: typeName conName args
  | Case Term [Clause]           -- pattern matching elimination
  | Meta Int                     -- metavariable (for unification)
  | Proj Int Term                -- projection (record/structure)
  | Fix FixInfo Term             -- fixpoint (primitive recursion)
  | Refl Term                    -- equality witness
  | Eq Term Term Term            -- @Eq A x y
  | Annot Term Term              -- (e : T)
  | NatLit Int
  | CharLit Int
  | StringLit String
  | Hole String
  deriving (Eq, Show)

-- Binder: explicit or implicit parameter
data Binder
  = BExplicit Name Term          -- (x : A)
  | BImplicit Name Term          -- {x : A}
  deriving (Eq, Show)

-- Inductive definition (families)
data IndDef = IndDef
  { indName    :: String
  , indParams  :: [Binder]       -- parameters (shared across constructors)
  , indIndices :: [Binder]       -- indices (vary per constructor)
  , indSort    :: Sort             -- target universe
  , indConstrs :: [ConstrDef]
  } deriving (Eq, Show)

data ConstrDef = ConstrDef
  { conName   :: String
  , conArgs   :: [Binder]        -- constructor arguments
  , conResult :: [Term]            -- indices in return type (applied to params)
  } deriving (Eq, Show)

-- Pattern matching clause
data Clause = Clause Pattern Term deriving (Eq, Show)

data Pattern
  = PVar Name
  | PCon String [Pattern]
  | PLit Int
  | PWild
  | PInaccessible Term          -- inaccessible pattern (dot pattern)
  | PAnnotated Pattern Term
  deriving (Eq, Show)

-- Fixpoint info for structural recursion
data FixInfo = FixInfo
  { fixName   :: Name
  , fixType   :: Term
  , fixRecArg :: Int               -- which argument is the decreasing one
  } deriving (Eq, Show)

-- Declarations
data Decl
  = TypeSig String Term
  | FunDef String [Clause]
  | IndDecl IndDef
  | InfixDecl Fixity Int [String]
  | AxiomDecl String Term          -- postulate/axiom
  deriving (Eq, Show)

data Fixity = Infix | InfixL | InfixR deriving (Eq, Show)

type Program = [Decl]

-- ============================================
-- PRETTY PRINTING
-- ============================================
ppName (Raw s)    = s
ppName (Ind i)    = "v" ++ show i
ppName (Global s) = s

ppLevel LZero     = "0"
ppLevel (LSucc u) = "(succ " ++ ppLevel u ++ ")"
ppLevel (LMax u v) = "(max " ++ ppLevel u ++ " " ++ ppLevel v ++ ")"
ppLevel (LVar s)  = "u_" ++ s

ppSort SProp         = "Prop"
ppSort (SType LZero) = "Type"
ppSort (SType u)     = "Type " ++ ppLevel u
ppSort (SSucc s)     = "Sort (" ++ ppSort s ++ " + 1)"

ppBinder (BExplicit n t) = "(" ++ ppName n ++ " : " ++ ppTerm t ++ ")"
ppBinder (BImplicit n t) = "{" ++ ppName n ++ " : " ++ ppTerm t ++ "}"

ppTerm (Var n)       = ppName n
ppTerm (App f x)     = "(" ++ ppTerm f ++ " " ++ ppTerm x ++ ")"
ppTerm (Lam b body)  = "(fun " ++ ppBinder b ++ " => " ++ ppTerm body ++ ")"
ppTerm (Pi b body)   = case b of
  BExplicit (Raw "_") t -> "(" ++ ppTerm t ++ " -> " ++ ppTerm body ++ ")"
  _ -> "(forall " ++ ppBinder b ++ ", " ++ ppTerm body ++ ")"
ppTerm (Let n ty val body) = "(let " ++ ppName n ++ " : " ++ ppTerm ty ++ " := " ++ ppTerm val ++ " in " ++ ppTerm body ++ ")"
ppTerm (Sort s)      = ppSort s
ppTerm (Inductive d) = "<inductive " ++ indName d ++ ">"
ppTerm (Constr tn cn args) = "(" ++ cn ++ foldr (\a r -> " " ++ ppTerm a ++ r) "" args ++ ")"
ppTerm (Case e cs)   = "(match " ++ ppTerm e ++ " with " ++ intercalate " | " (map (\(Clause p r) -> ppPat p ++ " => " ++ ppTerm r) cs) ++ ")"
ppTerm (Meta i)      = "?_" ++ show i
ppTerm (Proj i e)    = "(proj" ++ show i ++ " " ++ ppTerm e ++ ")"
ppTerm (Fix _ t)     = "(fix " ++ ppTerm t ++ ")"
ppTerm (Refl e)      = "(Refl " ++ ppTerm e ++ ")"
ppTerm (Eq a x y)    = "(@Eq " ++ ppTerm a ++ " " ++ ppTerm x ++ " " ++ ppTerm y ++ ")"
ppTerm (Annot e t)   = "(" ++ ppTerm e ++ " : " ++ ppTerm t ++ ")"
ppTerm (NatLit n)    = show n
ppTerm (CharLit c)   = "'" ++ chr c : "'"
ppTerm (StringLit s) = "\"" ++ s ++ "\""
ppTerm (Hole h)      = "?" ++ h

ppPat (PVar n)       = ppName n
ppPat (PCon c ps)    = "(" ++ c ++ " " ++ unwords (map ppPat ps) ++ ")"
ppPat (PLit n)       = show n
ppPat PWild          = "_"
ppPat (PInaccessible t)= "." ++ ppTerm t
ppPat (PAnnotated p t)= "(" ++ ppPat p ++ " : " ++ ppTerm t ++ ")"

-- ============================================
-- DE BRUIJN CONVERSION
-- ============================================
toDeBruijn :: [(Name, Int)] -> Term -> Term
toDeBruijn env t = case t of
  Var n -> case lookup n env of
    Just i -> Var (Ind i)
    Nothing -> Var n
  App f x -> App (toDeBruijn env f) (toDeBruijn env x)
  Lam (BExplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Lam (BExplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Lam (BImplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Lam (BImplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Pi (BExplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Pi (BExplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Pi (BImplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Pi (BImplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Let n ty val b ->
    let env' = (n, 0) : map (second (+1)) env
    in Let (Ind 0) (toDeBruijn env ty) (toDeBruijn env val) (toDeBruijn env' (shift 1 b))
  Case e cs -> Case (toDeBruijn env e) (map (\(Clause p r) -> Clause (toDBPat p) (toDeBruijn (patEnv p env) r)) cs)
  Eq a x y -> Eq (toDeBruijn env a) (toDeBruijn env x) (toDeBruijn env y)
  Refl e -> Refl (toDeBruijn env e)
  Annot e t' -> Annot (toDeBruijn env e) (toDeBruijn env t')
  Proj i e -> Proj i (toDeBruijn env e)
  Fix info t' -> Fix info (toDeBruijn env t')
  _ -> t

shift :: Int -> Term -> Term
shift k t = case t of
  Var (Ind i) -> Var (Ind $ if i < k then i else i + 1)
  Var n -> Var n
  App f x -> App (shift k f) (shift k x)
  Lam (BExplicit n ty) b -> Lam (BExplicit n (shift k ty)) (shift (k+1) b)
  Lam (BImplicit n ty) b -> Lam (BImplicit n (shift k ty)) (shift (k+1) b)
  Pi (BExplicit n ty) b -> Pi (BExplicit n (shift k ty)) (shift (k+1) b)
  Pi (BImplicit n ty) b -> Pi (BImplicit n (shift k ty)) (shift (k+1) b)
  Let n ty val b -> Let n (shift k ty) (shift k val) (shift (k+1) b)
  Case e cs -> Case (shift k e) (map (\(Clause p r) -> Clause (shiftPat k p) (shift k r)) cs)
  Eq a x y -> Eq (shift k a) (shift k x) (shift k y)
  Refl e -> Refl (shift k e)
  Annot e t' -> Annot (shift k e) (shift k t')
  Proj i e -> Proj i (shift k e)
  Fix info t' -> Fix info (shift k t')
  _ -> t

toDBPat :: Pattern -> Pattern
toDBPat p = case p of
  PVar n -> PVar (Ind 0)
  PCon c ps -> PCon c (map toDBPat ps)
  PLit n -> PLit n
  PWild -> PWild
  PInaccessible t -> PInaccessible (shift (patDepth p) t)
  PAnnotated p' t -> PAnnotated (toDBPat p') (shift (patDepth p') t)

patEnv :: Pattern -> [(Name, Int)] -> [(Name, Int)]
patEnv p env = case p of
  PVar n -> (n, 0) : map (second (+1)) env
  PCon _ ps -> foldr (\p' e -> patEnv p' e) env ps
  PLit _ -> env
  PWild -> env
  PInaccessible _ -> env
  PAnnotated p' _ -> patEnv p' env

patDepth :: Pattern -> Int
patDepth p = case p of
  PVar _ -> 1
  PCon _ ps -> sum (map patDepth ps)
  PLit _ -> 0
  PWild -> 0
  PInaccessible _ -> 0
  PAnnotated p' _ -> patDepth p'

shiftPat :: Int -> Pattern -> Pattern
shiftPat k p = case p of
  PVar (Ind i) -> PVar (Ind $ if i < k then i else i + 1)
  PCon c ps -> PCon c (map (shiftPat k) ps)
  _ -> p

-- ============================================
-- SUBSTITUTION
-- ============================================
substitute :: Term -> Name -> Term -> Term
substitute val n t = case t of
  Var n' | n == n' -> val
         | otherwise -> Var n'
  App f x -> App (substitute val n f) (substitute val n x)
  Lam (BExplicit n' ty) b ->
    if n == n' then Lam (BExplicit n' (substitute val n ty)) b
    else Lam (BExplicit n' (substitute val n ty)) (substitute val n b)
  Lam (BImplicit n' ty) b ->
    if n == n' then Lam (BImplicit n' (substitute val n ty)) b
    else Lam (BImplicit n' (substitute val n ty)) (substitute val n b)
  Pi (BExplicit n' ty) b ->
    if n == n' then Pi (BExplicit n' (substitute val n ty)) b
    else Pi (BExplicit n' (substitute val n ty)) (substitute val n b)
  Pi (BImplicit n' ty) b ->
    if n == n' then Pi (BImplicit n' (substitute val n ty)) b
    else Pi (BImplicit n' (substitute val n ty)) (substitute val n b)
  Let n' ty val' b ->
    if n == n' then Let n' (substitute val n ty) (substitute val n val') b
    else Let n' (substitute val n ty) (substitute val n val') (substitute val n b)
  Case e cs -> Case (substitute val n e) (map (\(Clause p r) -> (Clause p (substitute val n r))) cs)
  Refl e -> Refl (substitute val n e)
  Eq a x y -> Eq (substitute val n a) (substitute val n x) (substitute val n y)
  Annot e t' -> Annot (substitute val n e) (substitute val n t')
  Proj i e -> Proj i (substitute val n e)
  Fix info t' -> Fix info (substitute val n t')
  _ -> t
