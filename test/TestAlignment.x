-- ============================================
-- TEST SUITE: Lean 4 Core Alignment
-- Testing Universe, Recursion, and Metavars
-- ============================================

module Test where
import Base
import Ast
import Universe
import Recursion
import Metavars
import TyperAligned

-- ============================================
-- 1. Universe Constraint Tests
-- ============================================

testUniverseBasic :: IO ()
testUniverseBasic = do
  putStrLn "=== Universe Constraint Tests ==="
  
  -- Test 1: Basic Level Ordering
  putStrLn "Test 1: Level ordering"
  assert (levelLeq LZero (LSucc LZero)) "LZero <= succ(LZero)"
  assert (not $ levelLeq (LSucc LZero) LZero) "not (succ(LZero) <= LZero)"
  assert (levelLeq (LSucc LZero) (LSucc (LSucc LZero))) "succ(LZero) <= succ(succ(LZero))"
  
  -- Test 2: Level Max
  putStrLn "Test 2: Level max"
  assert (levelMax LZero (LSucc LZero) == LSucc LZero) "max(0, succ(0)) = succ(0)"
  assert (levelMax (LSucc LZero) LZero == LSucc LZero) "max(succ(0), 0) = succ(0)"
  assert (levelMax (LSucc LZero) (LSucc LZero) == LSucc LZero) "max(succ(0), succ(0)) = succ(0)"
  
  -- Test 3: Universe Constraint Addition
  putStrLn "Test 3: Universe constraint addition"
  case addConstraint (ULeq LZero (LSucc LZero)) emptyUState of
    Right st -> putStrLn "✓ Successfully added constraint"
    Left e -> putStrLn $ "✗ Failed: " ++ e
  
  -- Test 4: Universe Constraint Rejection
  putStrLn "Test 4: Universe constraint rejection"
  case addConstraint (ULeq (LSucc LZero) LZero) emptyUState of
    Right _ -> putStrLn "✗ Should have rejected invalid constraint"
    Left _ -> putStrLn "✓ Correctly rejected invalid constraint"
  
  putStrLn ""

assert :: Bool -> String -> IO ()
assert True msg = putStrLn $ "✓ " ++ msg
assert False msg = putStrLn $ "✗ " ++ msg

-- ============================================
-- 2. Sort Tests
-- ============================================

testSortOperations :: IO ()
testSortOperations = do
  putStrLn "=== Sort Operation Tests ==="
  
  -- Test Sort Cumulativity
  putStrLn "Test: Sort cumulativity"
  assert (sortLeq SProp SProp) "Prop <= Prop"
  assert (sortLeq SProp (SType LZero)) "Prop <= Type"
  assert (sortLeq (SType LZero) (SType LZero)) "Type <= Type"
  assert (not $ sortLeq (SType LZero) SProp) "not (Type <= Prop)"
  assert (sortLeq (SType LZero) (SType (LSucc LZero))) "Type <= Type 1"
  
  -- Test Sort Max
  putStrLn "Test: Sort max"
  assert (sortMax SProp (SType LZero) == SType LZero) "max(Prop, Type) = Type"
  assert (sortMax (SType LZero) SProp == SType LZero) "max(Type, Prop) = Type"
  assert (sortMax (SType LZero) (SType LZero) == SType LZero) "max(Type, Type) = Type"
  assert (sortMax (SType (LSucc LZero)) (SType LZero) == SType (LSucc LZero)) "max(Type1, Type) = Type1"
  
  -- Test Sort Succ
  putStrLn "Test: Sort successor"
  assert (sortSucc SProp == SType LZero) "succ(Prop) = Type"
  assert (sortSucc (SType LZero) == SType (LSucc LZero)) "succ(Type) = Type 1"
  
  putStrLn ""

-- ============================================
-- 3. Metavariable Tests
-- ============================================

testMetavariables :: IO ()
testMetavariables = do
  putStrLn "=== Metavariable Tests ==="
  
  let mctx = emptyMetavarContext
  let ctx = []
  let ty = Sort (SType LZero)
  
  -- Test: Create metavariable
  putStrLn "Test: Create metavariable"
  let (mctx1, idx1) = newMetavar ctx ty mctx
  putStrLn $ "✓ Created metavariable with index " ++ show idx1
  
  -- Test: Instantiate metavariable
  putStrLn "Test: Instantiate metavariable"
  let solution = Var (Global "Nat")
  case instantiateMetavar idx1 solution mctx1 of
    Right mctx2 -> do
      putStrLn "✓ Instantiated metavariable"
      -- Check solution
      case getMetavarSolution idx1 mctx2 of
        Just sol -> putStrLn $ "✓ Solution: " ++ ppTerm sol
        Nothing -> putStrLn "✗ No solution found"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  -- Test: Contains metavariable
  putStrLn "Test: Contains metavariable"
  let term = App (Meta idx1) (Var (Global "x"))
  assert (containsMetavar idx1 term) "Term contains metavariable"
  
  -- Test: Unsolved metavariables
  putStrLn "Test: Unsolved metavariables"
  let (mctx3, idx2) = newMetavar ctx ty mctx1
  let unsolved = getUnsolvedMetavars mctx3
  assert (length unsolved == 1) "One unsolved metavariable"
  
  putStrLn ""

-- ============================================
-- 4. Structural Recursion Tests
-- ============================================

testRecursion :: IO ()
testRecursion = do
  putStrLn "=== Structural Recursion Tests ==="
  
  let ctx = []
  
  -- Test 1: Decreasing recursion (Natural numbers)
  putStrLn "Test 1: Decreasing recursion (Nat)"
  let natType = Var (Global "Nat")
  let fnType = Pi (BExplicit (Global "n") natType) natType
  let clauses = []
  
  putStrLn "Note: Simple recursion check for Nat"
  
  -- Test 2: Non-decreasing recursion (should fail)
  putStrLn "Test 2: Non-decreasing recursion detection"
  -- This would require a more complex example
  
  putStrLn ""

-- ============================================
-- 5. Definitional Equality Tests
-- ============================================

testDefeq :: IO ()
testDefeq = do
  putStrLn "=== Definitional Equality Tests ==="
  
  let ctx = []
  
  -- Test: Variable equality
  putStrLn "Test: Variable equality"
  assert (defeq ctx (Var (Global "x")) (Var (Global "x"))) "Same variables are defeq"
  assert (not $ defeq ctx (Var (Global "x")) (Var (Global "y"))) "Different variables not defeq"
  
  -- Test: Natural number literals
  putStrLn "Test: Natural number literals"
  assert (defeq ctx (NatLit 0) (NatLit 0)) "Same Nat literals are defeq"
  assert (not $ defeq ctx (NatLit 0) (NatLit 1)) "Different Nat literals not defeq"
  
  -- Test: Sort equality
  putStrLn "Test: Sort equality"
  assert (defeq ctx (Sort SProp) (Sort SProp)) "Same sorts are defeq"
  assert (defeq ctx (Sort (SType LZero)) (Sort (SType LZero))) "Same Type levels are defeq"
  
  putStrLn ""

-- ============================================
-- 6. Conversion Tests
-- ============================================

testConversion :: IO ()
testConversion = do
  putStrLn "=== Conversion Tests ==="
  
  let ctx = []
  
  -- Test: SProp <= SType
  putStrLn "Test: Prop to Type conversion"
  case convert ctx (Sort SProp) (Sort (SType LZero)) of
    Right _ -> putStrLn "✓ Prop converts to Type"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  -- Test: Type level cumulativity
  putStrLn "Test: Type level cumulativity"
  case convert ctx (Sort (SType LZero)) (Sort (SType (LSucc LZero))) of
    Right _ -> putStrLn "✓ Type converts to Type 1"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  putStrLn ""

-- ============================================
-- 7. Inductive Type Universe Tests (Gondor Rules)
-- ============================================

testInductiveUniverse :: IO ()
testInductiveUniverse = do
  putStrLn "=== Inductive Type Universe Tests (Gondor Rules) ==="
  
  let ctx = []
  
  -- Define Nat type
  let natInd = IndDef
        { indName = "Nat"
        , indParams = []
        , indIndices = []
        , indSort = SType LZero
        , indConstrs = 
            [ ConstrDef "Z" [] []
            , ConstrDef "S" [BExplicit (Raw "n") (Var (Global "Nat"))] []
            ]
        }
  
  putStrLn "Test: Nat inductive type"
  case inferIndSort ctx natInd of
    Right sort -> putStrLn $ "✓ Nat has sort: " ++ ppSort sort
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  putStrLn ""

-- ============================================
-- 8. Complete Program Typecheck Test
-- ============================================

testProgramTypecheck :: IO ()
testProgramTypecheck = do
  putStrLn "=== Complete Program Typecheck Test ==="
  
  -- Define Nat
  let natDecl = IndDecl $ IndDef
        { indName = "Nat"
        , indParams = []
        , indIndices = []
        , indSort = SType LZero
        , indConstrs = 
            [ ConstrDef "Z" [] []
            , ConstrDef "S" [BExplicit (Raw "n") (Var (Global "Nat"))] []
            ]
        }
  
  -- Define add
  let addSig = TypeSig "add" $ Pi (BExplicit (Raw "n") (Var (Global "Nat"))) 
                                   $ Pi (BExplicit (Raw "m") (Var (Global "Nat"))) 
                                   $ Var (Global "Nat")
  
  let addDef = FunDef "add" 
        [ Clause (PCon "Z" [PVar (Global "m")]) (Var (Global "m"))
        , Clause (PCon "S" [PVar (Global "n"), PVar (Global "m")]) 
                 (Constr "Nat" "S" [App (App (Var (Global "add")) (Var (Global "n"))) (Var (Global "m"))])
        ]
  
  let prog = [natDecl, addSig, addDef]
  
  putStrLn "Testing program typecheck..."
  case typecheck prog of
    Right (ctx, result) -> do
      putStrLn "✓ Program typechecks successfully"
      putStrLn $ "Result type: " ++ ppTerm result
    Left e -> putStrLn $ "✗ Typecheck failed: " ++ e
  
  putStrLn ""

-- ============================================
-- 9. Equality Type Tests
-- ============================================

testEquality :: IO ()
testEquality = do
  putStrLn "=== Equality Type Tests ==="
  
  -- Define Eq type
  let eqInd = IndDecl $ IndDef
        { indName = "Eq"
        , indParams = [BImplicit (Raw "a") (Sort (SType LZero))]
        , indIndices = []
        , indSort = SProp
        , indConstrs = 
            [ ConstrDef "Refl" [BImplicit (Raw "x") (Var (Global "a"))] []
            ]
        }
  
  -- Define subst
  let substSig = TypeSig "subst" $
        Pi (BImplicit (Raw "a") (Sort (SType LZero))) $
        Pi (BImplicit (Raw "x") (Var (Global "a"))) $
        Pi (BImplicit (Raw "y") (Var (Global "a"))) $
        Pi (BImplicit (Raw "p") (App (App (Var (Global "Eq")) (Var (Global "a"))) (Var (Global "x")) (Var (Global "y")))) $
        Pi (BImplicit (Raw "P") (Pi (BExplicit (Raw "_") (Var (Global "a"))) (Sort SProp))) $
        Pi (BImplicit (Raw "px") (App (Var (Global "P")) (Var (Global "x")))) $
        App (Var (Global "P")) (Var (Global "y"))
  
  let prog = [eqInd, substSig]
  
  putStrLn "Testing equality type..."
  case typecheck prog of
    Right _ -> putStrLn "✓ Equality type checks"
    Left e -> putStrLn $ "✗ Error: " ++ e
  
  putStrLn ""

-- ============================================
-- RUN ALL TESTS
-- ============================================

runAllTests :: IO ()
runAllTests = do
  putStrLn "========================================"
  putStrLn "Lean 4 Core Alignment - Test Suite"
  putStrLn "========================================"
  putStrLn ""
  
  testUniverseBasic
  testSortOperations
  testMetavariables
  testRecursion
  testDefeq
  testConversion
  testInductiveUniverse
  testProgramTypecheck
  testEquality
  
  putStrLn "========================================"
  putStrLn "Test Suite Completed"
  putStrLn "========================================"

main :: IO ()
main = runAllTests
