module Universe where
import Base
import Ast

-- ============================================
-- UNIVERSE CONSTRAINT SOLVER
-- Lean 4 Core Alignment: Calculus of Inductive Constructions
-- ============================================

-- 约束类型定义
data UConstraint
  = ULeq Level Level
  | UEq Level Level
  | UMax Level Level Level
  deriving (Eq, Show)

-- Universe 状态
data UState = UState
  { usConstraints :: [UConstraint]
  , usSubst       :: Map Level Level
  , usMaxLevel    :: Level
  , usErrors      :: [String]
  } deriving (Show)

emptyUState :: UState
emptyUState = UState [] Tip LZero []

-- Level 比较
compareLevel :: Level -> Level -> Ordering
compareLevel LZero LZero = EQ
compareLevel LZero _ = LT
compareLevel _ LZero = GT
compareLevel (LSucc u) (LSucc v) = compareLevel u v
compareLevel u v = 
  if u == v then EQ 
  else case (u, v) of
    (LMax a b, _) -> undefined
    (_, LMax a b) -> undefined
    _ -> EQ

-- Level 相等性
levelEq :: Level -> Level -> Bool
levelEq LZero LZero = True
levelEq (LSucc u) (LSucc v) = levelEq u v
levelEq (LMax a b) (LMax c d) = 
  (levelEq a c && levelEq b d) || (levelEq a d && levelEq b c)
levelEq u v = u == v

-- Level 顺序: 检查 u <= v
levelLeq :: Level -> Level -> Bool
levelLeq LZero _ = True
levelLeq (LSucc u) (LSucc v) = levelLeq u v
levelLeq (LSucc _) LZero = False
levelLeq u (LMax v w) = levelLeq u v && levelLeq u w
levelLeq u v = u == v

-- Level Max
levelMax :: Level -> Level -> Level
levelMax LZero u = u
levelMax u LZero = u
levelMax (LSucc u) (LSucc v) = LSucc (levelMax u v)
levelMax u (LMax v w) = LMax u v w
levelMax u v = if levelLeq u v then v else if levelLeq v u then u else LMax u v

-- Level Succ
levelSucc :: Level -> Level
levelSucc = LSucc

-- 规范化 Level
normalizeLevel :: Level -> UState -> Level
normalizeLevel LZero _ = LZero
normalizeLevel l@(LVar _) st = 
  case mlookup l (usSubst st) of
    Just l' -> normalizeLevel l' st
    Nothing -> l
normalizeLevel (LSucc u) st = LSucc (normalizeLevel u st)
normalizeLevel (LMax u v) st = 
  levelMax (normalizeLevel u st) (normalizeLevel v st)

-- 添加约束
addConstraint :: UConstraint -> UState -> Either String UState
addConstraint c st = do
  c' <- normalizeConstraint c st
  if isRedundant c' (usConstraints st)
     then Right st
     else do
       st' <- propagate c' st
       Right $ st' { usConstraints = c' : usConstraints st' }

normalizeConstraint :: UConstraint -> UState -> Either String UConstraint
normalizeConstraint (ULeq u v) st = Right $ ULeq (normalizeLevel u st) (normalizeLevel v st)
normalizeConstraint (UEq u v) st = Right $ UEq (normalizeLevel u st) (normalizeLevel v st)
normalizeConstraint (UMax u v w) st = 
  Right $ UMax (normalizeLevel u st) (normalizeLevel v st) (normalizeLevel w st)

isRedundant :: UConstraint -> [UConstraint] -> Bool
isRedundant c [] = False
isRedundant (ULeq u v) (c:cs) = 
  case c of
    UEq u' v' | u' == u && v' == v -> True
    ULeq u' v' | u' == u && v' == v -> True
    ULeq u' v' | levelLeq u' u && v == v' -> True
    _ -> isRedundant (ULeq u v) cs
isRedundant c (_:cs) = isRedundant c cs

propagate :: UConstraint -> UState -> Either String UState
propagate c st = case c of
  ULeq u v -> do
    let newCs = [ULeq u' v | ULeq v' v' <- usConstraints st, levelEq u' v']
    foldM addConstraint st newCs
  UEq u v -> do
    st1 <- addConstraint (ULeq u v) st
    addConstraint (ULeq v u) st1
  UMax u v w -> do
    st1 <- addConstraint (ULeq w u) st
    st2 <- addConstraint (ULeq w v) st1
    Right st2

-- 检查约束是否满足
checkConstraints :: [UConstraint] -> Either String ()
checkConstraints cs = 
  if all checkOne (reverse cs)
     then Right ()
     else Left "Universe constraints violated"
  where
    checkOne (ULeq u v) = levelLeq (normalizeLevel u emptyUState) 
                               (normalizeLevel v emptyUState)
    checkOne (UEq u v) = levelEq (normalizeLevel u emptyUState) 
                               (normalizeLevel v emptyUState)
    checkOne (UMax u v w) = 
      let w' = levelMax u v
      in levelEq (normalizeLevel w emptyUState) 
                 (normalizeLevel w' emptyUState)

-- 推断 Term 的 Level
inferLevel :: Ctx -> Term -> Either String Level
inferLevel ctx t = case whnf ctx t of
  Sort (SType u) -> Right u
  Sort SProp -> Right LZero
  Var n -> case lookupType n ctx of
    Just ty -> inferLevel ctx ty
    Nothing -> Left $ "Cannot infer level of: " ++ ppName n
  Pi b body -> do
    a <- inferLevel ctx (binderType b)
    b' <- inferLevel (extendCtxBinder ctx b) body
    Right $ levelMax a b'
  App f x -> do
    af <- inferLevel ctx f
    ax <- inferLevel ctx x
    Right $ levelMax af ax
  Lam b body -> inferLevel (extendCtxBinder ctx b) body
  Let n ty val body -> inferLevel (extend n ty (Just val) ctx) body
  _ -> Left $ "Cannot infer level of: " ++ ppTerm t

-- Sort 累积性检查
sortLeq :: Sort -> Sort -> Bool
sortLeq SProp SProp = True
sortLeq SProp (SType _) = True
sortLeq SProp (SSucc _) = True
sortLeq (SType u) (SType v) = levelLeq u v
sortLeq (SType _) SProp = False
sortLeq (SSucc s1) (SSucc s2) = sortLeq s1 s2
sortLeq s1 s2 = s1 == s2

-- Sort Succ
sortSucc :: Sort -> Sort
sortSucc SProp = SType LZero
sortSucc (SType u) = SType (levelSucc u)
sortSucc (SSucc s) = SSucc (sortSucc s)

-- Sort Max
sortMax :: Sort -> Sort -> Sort
sortMax SProp s = s
sortMax s SProp = s
sortMax (SType u) (SType v) = SType (levelMax u v)
sortMax s1 s2 = if sortLeq s1 s2 then s2 else s1

-- Sort Level
sortLevel :: Sort -> Level
sortLevel SProp = LZero
sortLevel (SType u) = u
sortLevel (SSucc s) = levelSucc (sortLevel s)

-- 推断 Sort
inferSort :: Ctx -> Term -> Either String Sort
inferSort ctx t = do
  ty <- infer ctx t
  case whnf ctx ty of
    Sort s -> Right s
    _ -> Left $ "Expected sort, got: " ++ ppTerm ty

-- 检查 Sort
checkSort :: Ctx -> Term -> Sort -> Either String ()
checkSort ctx t expected = do
  actual <- inferSort ctx t
  if sortLeq actual expected
     then Right ()
     else Left $ "Sort mismatch: " ++ ppSort actual ++ " not <= " ++ ppSort expected

-- 推断归纳定义 Sort
inferIndSort :: Ctx -> IndDef -> Either String Sort
inferIndSort ctx ind = do
  paramLevels <- mapM (inferLevel ctx) (map binderType (indParams ind))
  let paramCtx = foldr extendCtxBinder ctx (indParams ind)
  indexLevels <- mapM (inferLevel paramCtx) (map binderType (indIndices ind))
  let fullCtx = foldr extendCtxBinder paramCtx (indIndices ind)
  mapM_ (checkConstrSort fullCtx paramLevels indexLevels) (indConstrs ind)
  let resultLevel = foldr levelMax LZero (paramLevels ++ indexLevels)
  Right $ SType resultLevel

checkConstrSort :: Ctx -> [Level] -> [Level] -> ConstrDef -> Either String ()
checkConstrSort ctx paramLevels indexLevels con = do
  argLevels <- mapM (inferLevel ctx) (map binderType (conArgs con))
  let conLevel = foldr levelMax LZero (paramLevels ++ indexLevels ++ argLevels)
  if levelLeq conLevel (foldr levelMax LZero (paramLevels ++ indexLevels))
     then Right ()
     else Left $ "Constructor universe too large: " ++ ppLevel conLevel

-- 检查 Universe 多态性
checkUniversePolymorphism :: Ctx -> Term -> Either String ()
checkUniversePolymorphism ctx t = case t of
  Pi b body -> do
    checkUniversePolymorphism ctx (binderType b)
    checkUniversePolymorphism (extendCtxBinder ctx b) body
  Lam b body -> do
    checkUniversePolymorphism ctx (binderType b)
    checkUniversePolymorphism (extendCtxBinder ctx b) body
  App f x -> do
    checkUniversePolymorphism ctx f
    checkUniversePolymorphism ctx x
  Sort _ -> Right ()
  Var _ -> Right ()
  _ -> Right ()

-- 生成 Universe 约束
generateUConstraints :: Ctx -> Term -> Term -> UState -> Either String UState
generateUConstraints ctx t1 t2 st = do
  s1 <- inferSort ctx t1
  s2 <- inferSort ctx t2
  let c = ULeq (sortLevel s1) (sortLevel s2)
  addConstraint c st

-- 统一 Sort
unifySorts :: Sort -> Sort -> UState -> Either String UState
unifySorts SProp SProp st = Right st
unifySorts (SType u1) (SType u2) st = 
  addConstraint (UEq u1 u2) st
unifySorts s1 s2 _ = Left $ "Cannot unify sorts: " ++ ppSort s1 ++ " with " ++ ppSort s2

-- Pretty print Level
ppLevel :: Level -> String
ppLevel LZero = "0"
ppLevel (LSucc u) = "(succ " ++ ppLevel u ++ ")"
ppLevel (LMax u v) = "(max " ++ ppLevel u ++ " " ++ ppLevel v ++ ")"
ppLevel (LVar s) = "u_" ++ s

-- Pretty print Sort
ppSort :: Sort -> String
ppSort SProp = "Prop"
ppSort (SType LZero) = "Type"
ppSort (SType u) = "Type " ++ ppLevel u
ppSort (SSucc s) = "(" ++ ppSort s ++ ")"

-- 测试函数
testUniverseSolver :: IO ()
testUniverseSolver = do
  putStrLn "Testing Universe Constraint Solver..."
  
  let st1 = emptyUState
  case addConstraint (ULeq LZero (LSucc LZero)) st1 of
    Right st -> putStrLn $ "✓ Added constraint: 0 <= succ 0"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  case addConstraint (ULeq (LSucc LZero) LZero) emptyUState of
    Right _ -> putStrLn "✗ Should have failed: succ 0 <= 0"
    Left e -> putStrLn $ "✓ Correctly rejected: " ++ e
  
  case checkConstraints [ULeq LZero (LSucc LZero), ULeq (LSucc LZero) (LSucc (LSucc LZero))] of
    Right _ -> putStrLn "✓ Constraints satisfied"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  putStrLn "Universe solver tests completed."
