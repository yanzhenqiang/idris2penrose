module Metavars where
import Base
import Ast
import Universe

-- ============================================
-- METAVARIABLE SYSTEM
-- Lean 4 Core Alignment: Meta Variable Handling
-- ============================================

-- 元变量实例
data Metavar = Metavar
  { mvIndex     :: Int
  , mvName      :: String
  , mvType      :: Term
  , mvCtx       :: Ctx
  , mvSolution  :: Maybe Term
  , mvDelayed   :: [(Name, Term)]
  , mvPending   :: [(Int, Term)]
  } deriving (Show)

-- 元变量上下文
data MetavarContext = MetavarContext
  { mvCounter   :: Int
  , mvNextName  :: Int
  , mvStore     :: Map Int Metavar
  , mvInstances :: Map Int Term
  } deriving (Show)

emptyMetavarContext :: MetavarContext
emptyMetavarContext = MetavarContext 0 0 Tip Tip

-- 创建新元变量
newMetavar :: Ctx -> Term -> MetavarContext 
           -> (MetavarContext, Int)
newMetavar ctx ty mctx = 
  let idx = mvCounter mctx
      name = "M" ++ show (mvNextName mctx)
      mv = Metavar idx name ty ctx Nothing [] []
      mctx' = mctx { mvCounter = idx + 1
                   , mvNextName = mvNextName mctx + 1
                   , mvStore = insert idx mv (mvStore mctx) }
  in (mctx', idx)

-- 实例化元变量
instantiateMetavar :: Int -> Term -> MetavarContext 
                   -> Either String MetavarContext
instantiateMetavar idx solution mctx = 
  case mlookup idx (mvStore mctx) of
    Nothing -> Left $ "Unknown metavariable: ?" ++ show idx
    Just mv -> do
      solution' <- applyDelayedSubstitutions (mvDelayed mv) solution
      let mv' = mv { mvSolution = Just solution' }
      let mctx' = mctx { mvStore = insert idx mv' (mvStore mctx) }
      propagateInstantiation idx solution' mctx'

-- 应用延迟替换
applyDelayedSubstitutions :: [(Name, Term)] -> Term 
                          -> Either String Term
applyDelayedSubstitutions subs t = 
  foldM (\term (name, val) -> substitute val name term) t subs

-- 传播实例化
propagateInstantiation :: Int -> Term -> MetavarContext 
                       -> Either String MetavarContext
propagateInstantiation solvedIdx solution mctx = 
  let allPending = concatMap mvPending (elems (mvStore mctx))
      affectedMvars = filter (containsMetavar solvedIdx . snd) allPending
  foldM (propagateTo solvedIdx solution) mctx affectedMvars

propagateTo :: Int -> Term -> MetavarContext -> (Int, Term) 
            -> Either String MetavarContext
propagateTo solvedIdx solution mctx (depIdx, term) = 
  if containsMetavar solvedIdx term
     then do
       let term' = substitute solution (Meta solvedIdx) term
       instantiateMetavar depIdx term' mctx
     else Right mctx

-- 检查项是否包含特定元变量
containsMetavar :: Int -> Term -> Bool
containsMetavar idx t = case t of
  Meta i -> i == idx
  App f a -> containsMetavar idx f || containsMetavar idx a
  Lam b body -> containsMetavar idx (binderType b) 
             || containsMetavar idx body
  Pi b body -> containsMetavar idx (binderType b) 
            || containsMetavar idx body
  Let n ty val body -> containsMetavar idx ty 
                     || containsMetavar idx val 
                     || containsMetavar idx body
  Case e ps -> containsMetavar idx e 
             || any (\(Clause p r) -> containsMetavar idx r) ps
  Eq a x y -> any (containsMetavar idx) [a, x, y]
  Refl e -> containsMetavar idx e
  Annot e t -> containsMetavar idx e || containsMetavar idx t
  Proj i e -> containsMetavar idx e
  Fix _ body -> containsMetavar idx body
  Constr _ _ args -> any (containsMetavar idx) args
  _ -> False

-- 解决所有元变量
solveAllMetavars :: MetavarContext -> Term -> Either String Term
solveAllMetavars mctx t = case t of
  Meta i -> case mlookup i (mvStore mctx) of
    Just mv -> case mvSolution mv of
      Just sol -> solveAllMetavars mctx sol
      Nothing -> Left $ "Unsolved metavariable: ?" ++ mvName mv
    Nothing -> Left $ "Unknown metavariable: ?" ++ show i
  App f a -> do
    f' <- solveAllMetavars mctx f
    a' <- solveAllMetavars mctx a
    return $ App f' a'
  Lam b body -> do
    let ty' = solveAllMetavars mctx (binderType b)
    body' <- solveAllMetavars mctx body
    return $ Lam (updateBinderType b ty') body'
  Pi b body -> do
    let ty' = solveAllMetavars mctx (binderType b)
    body' <- solveAllMetavars mctx body
    return $ Pi (updateBinderType b ty') body'
  Let n ty val body -> do
    ty' <- solveAllMetavars mctx ty
    val' <- solveAllMetavars mctx val
    body' <- solveAllMetavars mctx body
    return $ Let n ty' val' body'
  Case e ps -> do
    e' <- solveAllMetavars mctx e
    ps' <- mapM solveClause ps
    return $ Case e' ps'
  Eq a x y -> do
    a' <- solveAllMetavars mctx a
    x' <- solveAllMetavars mctx x
    y' <- solveAllMetavars mctx y
    return $ Eq a' x' y'
  Refl e -> do
    e' <- solveAllMetavars mctx e
    return $ Refl e'
  Annot e t -> do
    e' <- solveAllMetavars mctx e
    t' <- solveAllMetavars mctx t
    return $ Annot e' t'
  Proj i e -> do
    e' <- solveAllMetavars mctx e
    return $ Proj i e'
  Fix info body -> do
    body' <- solveAllMetavars mctx body
    return $ Fix info body'
  Constr tn cn args -> do
    args' <- mapM (solveAllMetavars mctx) args
    return $ Constr tn cn args'
  _ -> Right t

-- 解决子句
solveClause :: Clause -> Either String Clause
solveClause (Clause p rhs) = do
  rhs' <- solveAllMetavars undefined rhs
  return $ Clause p rhs'

-- 更新 binder 类型
updateBinderType :: Binder -> Term -> Binder
updateBinderType (BExplicit n _) ty = BExplicit n ty
updateBinderType (BImplicit n _) ty = BImplicit n ty

-- 检查是否有未解决的元变量
hasUnsolvedMetavars :: MetavarContext -> Term -> Bool
hasUnsolvedMetavars mctx t = case t of
  Meta i -> case mlookup i (mvStore mctx) of
    Just mv -> isNothing (mvSolution mv)
    Nothing -> False
  _ -> any (hasUnsolvedMetavars mctx) (subterms t)

-- 获取所有未解决的元变量
getUnsolvedMetavars :: MetavarContext -> [Metavar]
getUnsolvedMetavars mctx = 
  filter (isNothing . mvSolution) (elems (mvStore mctx))

-- 添加延迟替换
addDelayedSubst :: Int -> Name -> Term -> MetavarContext 
               -> Either String MetavarContext
addDelayedSubst idx name val mctx = 
  case mlookup idx (mvStore mctx) of
    Nothing -> Left $ "Unknown metavariable: ?" ++ show idx
    Just mv -> do
      let mv' = mv { mvDelayed = (name, val) : mvDelayed mv }
      Right $ mctx { mvStore = insert idx mv' (mvStore mctx) }

-- 获取元变量的解
getMetavarSolution :: Int -> MetavarContext -> Maybe Term
getMetavarSolution idx mctx = 
  case mlookup idx (mvStore mctx) of
    Just mv -> mvSolution mv
    Nothing -> Nothing

-- 检查元类型一致性
checkMetaTypeConsistency :: Term -> Term -> Ctx -> Either String ()
checkMetaTypeConsistency expected actual ctx = do
  actualTy <- infer ctx actual
  convert ctx expected actualTy

-- 提升元变量上下文
liftMetavars :: Ctx -> Term -> Term
liftMetavars fromCtx t = 
  foldr (\(name, idx) -> substitute (Meta idx) name) t
        [(name, idx) | (idx, mv) <- toList (mvStore undefined)
                     , (name, _) <- zip (ctxNames fromCtx) [0..]]

ctxNames :: Ctx -> [Name]
ctxNames = map fst

-- 规范化元变量
normalizeMetavars :: MetavarContext -> Term -> Term
normalizeMetavars mctx t = case t of
  Meta i -> case getMetavarSolution i mctx of
    Just sol -> normalizeMetavars mctx sol
    Nothing -> t
  _ -> normalizeTerm (normalizeMetavars mctx) t

normalizeTerm :: (Term -> Term) -> Term -> Term
normalizeTerm f t = case t of
  App f' a -> App (f' f) (f a)
  Lam b body -> Lam (f (binderType b)) (f body)
  Pi b body -> Pi (f (binderType b)) (f body)
  _ -> t

-- 添加待解决的依赖
addPending :: Int -> Int -> Term -> MetavarContext 
           -> Either String MetavarContext
addPending depIdx srcIdx term mctx = 
  case mlookup depIdx (mvStore mctx) of
    Nothing -> Left $ "Unknown metavariable: ?" ++ show depIdx
    Just mv -> do
      let mv' = mv { mvPending = (srcIdx, term) : mvPending mv }
      Right $ mctx { mvStore = insert depIdx mv' (mvStore mctx) }

-- 清理已解决的元变量
cleanupMetavars :: MetavarContext -> MetavarContext
cleanupMetavars mctx = 
  let solved = filter (isJust . mvSolution) (elems (mvStore mctx))
      unsolved = filter (isNothing . mvSolution) (elems (mvStore mctx))
      store = foldr (\mv -> insert (mvIndex mv) mv) Tip solved
  in mctx { mvStore = store }

-- 获取子项
subterms :: Term -> [Term]
subterms t = case t of
  Var _ -> []
  App f a -> f : a : subterms f ++ subterms a
  Lam b body -> binderType b : body : subterms body
  Pi b body -> binderType b : body : subterms body
  Let _ ty val body -> ty : val : body : subterms body
  Sort _ -> []
  Inductive _ -> []
  Constr _ _ args -> args ++ concatMap subterms args
  Case e ps -> e : concatMap (\(Clause _ r) -> r : subterms r) ps
  Meta _ -> []
  Proj _ e -> e : subterms e
  Fix _ body -> body : subterms body
  Refl e -> e : subterms e
  Eq a x y -> a : x : y : subterms a ++ subterms x ++ subterms y
  Annot e t -> e : t : subterms e ++ subterms t
  NatLit _ -> []
  CharLit _ -> []
  StringLit _ -> []
  Hole _ -> []

-- 替换项中的元变量
replaceMetavars :: Map Int Term -> Term -> Term
replaceMetavars subst t = case t of
  Meta i -> case mlookup i subst of
    Just sol -> replaceMetavars subst sol
    Nothing -> t
  App f a -> App (replaceMetavars subst f) 
                  (replaceMetavars subst a)
  Lam b body -> Lam (replaceBinder subst b) 
                     (replaceMetavars subst body)
  Pi b body -> Pi (replaceBinder subst b) 
                    (replaceMetavars subst body)
  Let n ty val body -> Let n (replaceMetavars subst ty) 
                              (replaceMetavars subst val) 
                              (replaceMetavars subst body)
  Case e ps -> Case (replaceMetavars subst e) 
                     (map replaceClause ps)
  Eq a x y -> Eq (replaceMetavars subst a) 
                 (replaceMetavars subst x) 
                 (replaceMetavars subst y)
  Refl e -> Refl (replaceMetavars subst e)
  Annot e t -> Annot (replaceMetavars subst e) 
                       (replaceMetavars subst t)
  Proj i e -> Proj i (replaceMetavars subst e)
  Fix info body -> Fix info (replaceMetavars subst body)
  Constr tn cn args -> Constr tn cn (map (replaceMetavars subst) args)
  _ -> t

replaceBinder :: Map Int Term -> Binder -> Binder
replaceBinder subst (BExplicit n ty) = BExplicit n (replaceMetavars subst ty)
replaceBinder subst (BImplicit n ty) = BImplicit n (replaceMetavars subst ty)

replaceClause :: Clause -> Clause
replaceClause (Clause p rhs) = Clause p (replaceMetavars undefined rhs)

-- 测试元变量系统
testMetavarSystem :: IO ()
testMetavarSystem = do
  putStrLn "Testing Metavariable System..."
  
  let mctx = emptyMetavarContext
  let ctx = []
  let ty = Sort (SType LZero)
  
  let (mctx1, idx1) = newMetavar ctx ty mctx
  
  putStrLn $ "✓ Created metavariable ?M0 with index " ++ show idx1
  
  let solution = Var (Global "Nat")
  case instantiateMetavar idx1 solution mctx1 of
    Right mctx2 -> putStrLn $ "✓ Instantiated metavariable ?M0 with Nat"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  putStrLn "Metavariable system tests completed."
