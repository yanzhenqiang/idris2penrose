module Recursion where
import Base
import Ast
import Universe

-- ============================================
-- STRUCTURAL RECURSION CHECKER
-- Lean 4 Core Alignment: Termination Verification
-- ============================================

-- 递归信息
data RecInfo = RecInfo
  { recFnName    :: Name
  , recType      :: Term
  , recArgPos    :: Int
  , recDepth     :: Int
  } deriving (Show)

-- 递归调用
data RecCall = RecCall
  { rcFnName     :: Name
  , rcArgPos     :: Int
  , rcArg        :: Term
  , rcCtx        :: Ctx
  } deriving (Show)

-- 递减信息
data DecreaseInfo
  = Decreased Term
  | Same Term
  | NotDecreased String
  deriving (Show)

-- 递归检查状态
data RecState = RecState
  { rsCurrentFn  :: Maybe RecInfo
  , rsCalls      :: [RecCall]
  , rsMaxDepth   :: Int
  , rsErrors     :: [String]
  } deriving (Show)

emptyRecState :: RecState
emptyRecState = RecState Nothing [] 0 []

-- 检查函数定义的递归
checkRecFunction :: Ctx -> String -> Term -> [Clause] -> Either String ()
checkRecFunction ctx fnName fnType clauses = do
  let recInfo = RecInfo (Global fnName) fnType 0 0
      state = emptyRecState { rsCurrentFn = Just recInfo }
  
  state' <- checkClauses ctx recInfo clauses state
  
  if null (rsErrors state')
     then Right ()
     else Left $ unlines (rsErrors state')

-- 检查所有子句
checkClauses :: Ctx -> RecInfo -> [Clause] -> RecState 
             -> Either String RecState
checkClauses ctx info [] state = Right state
checkClauses ctx info (clause:clauses) state = do
  state' <- checkClause ctx info clause state
  checkClauses ctx info clauses state'

-- 检查单个子句
checkClause :: Ctx -> RecInfo -> Clause -> RecState 
            -> Either String RecState
checkClause ctx info (Clause pattern rhs) state = do
  (bindings, recArgType) <- inferPatternType ctx pattern
  let ctx' = bindings ++ ctx
  state' <- checkExpr ctx' info rhs state
  Right state'

-- 从模式推断类型
inferPatternType :: Ctx -> Pattern -> Either String (Ctx, Term)
inferPatternType ctx p = case p of
  PVar n -> Right ([(n, (Var (Global "?"), Nothing))], Var (Global "?"))
  PWild -> Right ([], Var (Global "?"))
  PLit n -> Right ([], Var (Global "Nat"))
  PCon c ps -> do
    ind <- lookupIndDefByConstr c
    conDef <- maybe (Left $ "Unknown constructor: " ++ c)
                    Right
                    (findConstr ind c)
    let argCtx = foldr (\b c -> extendCtxBinder c b) ctx (conArgs conDef)
    argTys <- mapM (\_ -> inferPatternType argCtx) ps
    let (bindings, _) = unzip argTys
    let resultTy = conResult conDef
    Right (concat bindings, resultTy)
  PAnnotated p' ty -> do
    inferSort ctx ty
    inferPatternType ctx p'
  PInaccessible t -> Right ([], t)

-- 检查表达式中的递归调用
checkExpr :: Ctx -> RecInfo -> Term -> RecState 
          -> Either String RecState
checkExpr ctx info t state = case whnf ctx t of
  App f args -> do
    state' <- checkExpr ctx info f state
    foldM (checkExpr ctx info) args state'
  
  Lam b body -> checkExpr (extendCtxBinder ctx b) info body state
  
  Case e clauses -> do
    state' <- checkExpr ctx info e state
    checkClauses ctx info clauses state'
  
  Let n ty val body -> do
    infer ctx ty
    infer ctx val
    checkExpr (extend n ty (Just val) ctx) info body state
  
  Constr _ _ args -> foldM (checkExpr ctx info) args state
  
  Var n -> 
    if n == recFnName info
       then checkRecursiveCall ctx info t state
       else Right state
  
  _ -> Right state

-- 检查递归调用
checkRecursiveCall :: Ctx -> RecInfo -> Term -> RecState 
                   -> Either String RecState
checkRecursiveCall ctx info call state =
  case analyzeCall ctx info call of
    Left err -> Right $ state { rsErrors = err : rsErrors state }
    Right decInfo -> do
      case decInfo of
        Decreased _ -> Right $ state { rsCalls = rc : rsCalls state }
        Same _ -> Right $ state { rsErrors = "Recursive call not decreasing: " ++ ppTerm call : rsErrors state }
        NotDecreased reason -> Right $ state { rsErrors = reason : rsErrors state }
  where
    rc = RecCall (recFnName info) (recArgPos info) call ctx

-- 分析递归调用
analyzeCall :: Ctx -> RecInfo -> Term -> Either String DecreaseInfo
analyzeCall ctx info call = do
  let recArg = getArg call (recArgPos info)
  recArgType <- infer ctx recArg
  decrease <- checkDecrease ctx recArgType recArg
  return decrease

-- 获取参数
getArg :: Term -> Int -> Term
getArg (App f _) 0 = f
getArg (App f a) n = getArg f (n - 1)
getArg t _ = t

-- 检查递减
checkDecrease :: Ctx -> Term -> Term -> Either String DecreaseInfo
checkDecrease ctx expected recArg = 
  case (whnf ctx expected, whnf ctx recArg) of
    (_, Var _) | defeq ctx expected recArg -> 
      Right $ NotDecreased "Same term"
    
    (App (Var (Global "Nat")) _, NatLit n) ->
      if n >= 0 
         then Right $ Same recArg
         else Right $ NotDecreased "Negative literal"
    
    (App (Constr tn "S" [k]) _, Constr tn' "S" [k']) ->
      if tn == tn'
         then do
           result <- checkDecrease ctx k k'
           case result of
             Decreased _ -> Right $ Decreased recArg
             Same _ -> Right $ Decreased recArg
             NotDecreased _ -> Right $ NotDecreased "Constructor argument not decreasing"
         else Right $ NotDecreased "Different inductive types"
    
    (App (Constr tn "Z") _, Constr tn' "Z") ->
      if tn == tn'
         then Right $ Decreased recArg
         else Right $ NotDecreased "Different inductive types"
    
    (App (Var (Global "List")) elemTy, Constr _ "Nil" []) ->
      Right $ Decreased recArg
    
    (App (Var (Global "List")) elemTy, Constr _ "Cons" [hd, tl]) -> do
      result <- checkDecrease (App (Var (Global "List")) elemTy) tl tl
      case result of
        Decreased _ -> Right $ Decreased recArg
        Same _ -> Right $ Decreased recArg
        NotDecreased _ -> Right $ NotDecreased "List tail not decreasing"
    
    _ -> Right $ NotDecreased $ "Unknown decrease pattern: " ++ ppTerm expected ++ " vs " ++ ppTerm recArg

-- 定义相等性
defeq :: Ctx -> Term -> Term -> Bool
defeq ctx a b = case (whnf ctx a, whnf ctx b) of
  (Var n1, Var n2) -> n1 == n2
  (App f1 x1, App f2 x2) -> defeq ctx f1 f2 && defeq ctx x1 x2
  (Lam b1 body1, Lam b2 body2) -> 
    defeq ctx (binderType b1) (binderType b2) &&
    defeq (extendCtxBinder ctx b1) body1 body2
  (Pi b1 body1, Pi b2 body2) -> 
    defeq ctx (binderType b1) (binderType b2) &&
    defeq (extendCtxBinder ctx b1) body1 body2
  (Sort s1, Sort s2) -> s1 == s2
  (Constr _ c1 args1, Constr _ c2 args2) -> 
    c1 == c2 && length args1 == length args2 &&
    all (uncurry (defeq ctx)) (zip args1 args2)
  (NatLit n1, NatLit n2) -> n1 == n2
  (CharLit c1, CharLit c2) -> c1 == c2
  (StringLit s1, StringLit s2) -> s1 == s2
  (Meta i, Meta j) -> i == j
  (Refl e1, Refl e2) -> defeq ctx e1 e2
  _ -> False

-- 查找归纳定义（简化版）
lookupIndDefByConstr :: String -> Either String IndDef
lookupIndDefByConstr c = 
  Left $ "Constructor not found: " ++ c

-- 查找构造器定义
findConstr :: IndDef -> String -> Maybe ConstrDef
findConstr ind c = 
  find (\cd -> conName cd == c) (indConstrs ind)

-- 检查 Fixpoint
checkFixpoint :: Ctx -> FixInfo -> Term -> Either String ()
checkFixpoint ctx info body = do
  let fnType = fixType info
  let recArgPos = fixRecArg info
  let recArgType = getNthArgType fnType recArgPos
  
  recArgType' <- whnf ctx recArgType
  
  case recArgType' of
    Var _ -> Right ()
    _ -> do
      result <- checkDecrease ctx recArgType' (Var (fixName info))
      case result of
        Decreased _ -> Right ()
        _ -> Left "Fixpoint not structurally decreasing"

-- 获取第 n 个参数类型
getNthArgType :: Term -> Int -> Term
getNthArgType (Pi b body) 0 = binderType b
getNthArgType (Pi _ body) n = getNthArgType body (n - 1)
getNthArgType _ _ = Sort SProp

-- 检查结构递归（简单版本）
checkStructuralRecursion :: Ctx -> Term -> Term -> Either String ()
checkStructuralRecursion ctx fnType body = do
  recArgPos <- findRecArgPosition fnType
  let recArgType = getNthArgType fnType recArgPos
  checkBodyRecursion ctx fnType recArgType body 0

-- 查找递归参数位置
findRecArgPosition :: Term -> Either String Int
findRecArgPosition (Pi b body) = do
  ty <- infer (extendCtxBinder emptyCtx b) body
  if isInductiveType ty
     then Right 0
     else do
       pos <- findRecArgPosition body
       Right (pos + 1)
  where
    emptyCtx = []
    isInductiveType (Var (Global "Nat")) = True
    isInductiveType (App (Var (Global "List")) _) = True
    isInductiveType _ = False
findRecArgPosition _ = Right 0

-- 检查体的递归
checkBodyRecursion :: Ctx -> Term -> Term -> Term -> Int 
                   -> Either String ()
checkBodyRecursion ctx fnType recArgType body depth = 
  if depth > 100
     then Left "Recursion too deep"
     else case whnf ctx body of
       Lam b bdy -> 
         checkBodyRecursion (extendCtxBinder ctx b) fnType recArgType bdy (depth + 1)
       
       Case e clauses -> do
         checkExprRecursion ctx fnType recArgType e (depth + 1)
         mapM_ (checkClauseRecursion ctx fnType recArgType) clauses
       
       App f args -> do
         checkExprRecursion ctx fnType recArgType f (depth + 1)
         mapM_ (checkExprRecursion ctx fnType recArgType) args
       
       _ -> Right ()

-- 检查表达式递归
checkExprRecursion :: Ctx -> Term -> Term -> Term -> Int 
                   -> Either String ()
checkExprRecursion ctx fnType recArgType expr depth =
  if depth > 100
     then Left "Recursion too deep"
     else case whnf ctx expr of
       Var n -> 
         if n == fixName
            then checkCallDecrease ctx recArgType expr
            else Right ()
       _ -> Right ()
  where
    fixName = case fnType of
      Pi b _ -> binderName b
      _ -> Global "?"

-- 检查调用是否递减
checkCallDecrease :: Ctx -> Term -> Term -> Either String ()
checkCallDecrease ctx recArgType call = do
  let recArg = getArg call (findPos recArgType)
  result <- checkDecrease ctx recArgType recArg
  case result of
    Decreased _ -> Right ()
    Same _ -> Left "Recursive call not decreasing"
    NotDecreased reason -> Left reason

-- 查找位置
findPos :: Term -> Int
findPos _ = 0

-- 测试递归检查
testRecursionChecker :: IO ()
testRecursionChecker = do
  putStrLn "Testing Structural Recursion Checker..."
  
  let ctx = []
  let natType = Var (Global "Nat")
  let fnType = Pi (BExplicit (Global "n") natType) natType
  
  let clauses = []
  
  case checkRecFunction ctx "test" fnType clauses of
    Right _ -> putStrLn "✓ Recursion check passed"
    Left e -> putStrLn $ "✗ Recursion check failed: " ++ e
  
  putStrLn "Recursion checker tests completed."
