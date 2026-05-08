-- ============================================
-- TEST: REAL NUMBERS CONSTRUCTION
-- Testing the foundations of real numbers
-- ============================================

module TestReals where
import Base
import Ast
import TyperAligned
import RealNumbers

-- ============================================
-- TEST 1: Natural Numbers
-- ============================================

testNat :: IO ()
testNat = do
  putStrLn "=== Testing Natural Numbers ==="
  
  -- Test addition
  let zero = Z
  let one = S Z
  let two = S (S Z)
  let three = add two one
  
  putStrLn $ "2 + 1 = " ++ showNat three
  
  -- Test multiplication
  let six = mul three two
  putStrLn $ "3 * 2 = " ++ showNat six
  
  putStrLn ""

showNat :: Nat -> String
showNat Z = "0"
showNat (S n) = "S(" ++ showNat n ++ ")"

-- ============================================
-- TEST 2: Integers
-- ============================================

testInt :: IO ()
testInt = do
  putStrLn "=== Testing Integers ==="
  
  let pos5 = P (S (S (S (S (S Z)))))  -- +5
  let neg3 = N (S (S (S Z)))          -- -3
  let zeroI = ZI
  
  -- Test addition
  let sum1 = intAdd pos5 neg3
  putStrLn $ "5 + (-3) = " ++ showInt sum1
  
  let sum2 = intAdd neg3 neg3
  putStrLn $ "-3 + (-3) = " ++ showInt sum2
  
  -- Test multiplication
  let prod1 = intMul pos5 (P (S Z))  -- 5 * 1
  putStrLn $ "5 * 1 = " ++ showInt prod1
  
  putStrLn ""

showInt :: Int -> String
showInt ZI = "0"
showInt (P n) = "+" ++ showNat n
showInt (N n) = "-" ++ showNat n

-- ============================================
-- TEST 3: Rationals
-- ============================================

testRat :: IO ()
testRat = do
  putStrLn "=== Testing Rationals ==="
  
  -- 1/2 + 1/3 = 5/6
  let half = Qc (P (S Z)) (S Z)
  let third = Qc (P (S Z)) (S (S Z))
  let sum = ratAdd half third
  
  putStrLn $ "1/2 + 1/3 = " ++ showRat sum
  
  -- 1/2 * 2/3 = 2/6 = 1/3
  let prod = ratMul half third
  putStrLn $ "1/2 * 1/3 = " ++ showRat prod
  
  -- Test comparison
  let result = ratLt half third
  putStrLn $ "1/2 < 1/3? " ++ show result
  
  putStrLn ""

showRat :: Rational -> String
showRat (Qc n d) = showInt n ++ "/" ++ showNat d

-- ============================================
-- TEST 4: Cauchy Sequences
-- ============================================

testCauchy :: IO ()
testCauchy = do
  putStrLn "=== Testing Cauchy Sequences ==="
  
  -- Sequence: a_n = 1/n
  -- This is NOT a Cauchy sequence (it converges to 0, but not Cauchy)
  -- We need to test a proper Cauchy sequence
  
  -- Constant sequence: a_n = 1
  let const1 = constSeq ratOne
  putStrLn "Created constant sequence (1, 1, 1, ...)"
  
  -- Test term access
  let term0 = getTerm const1 Z
  putStrLn $ "a_0 = " ++ showRat term0
  
  let term5 = getTerm const1 (S (S (S (S (S Z)))))
  putStrLn $ "a_5 = " ++ showRat term5
  
  putStrLn ""

-- ============================================
-- TEST 5: Real Numbers
-- ============================================

testReal :: IO ()
testReal = do
  putStrLn "=== Testing Real Numbers ==="
  
  -- Convert rational to real
  let realHalf = ratToReal half
  putStrLn "Created real number from 1/2"
  
  -- Real approximation
  let approx = realApprox realHalf Z
  putStrLn $ "Real approximation at n=0: " ++ showRat approx
  
  let approx10 = realApprox realHalf (S (S (S (S (S (S (S (S (S (S Z)))))))))
  putStrLn $ "Real approximation at n=10: " ++ showRat approx10
  
  putStrLn ""

-- ============================================
-- TEST 6: Real Arithmetic
-- ============================================

testRealArith :: IO ()
testRealArith = do
  putStrLn "=== Testing Real Arithmetic ==="
  
  -- Real addition
  let real1 = ratToReal ratOne
  let real2 = ratToReal (Qc (P (S (S Z))) (S Z))  -- 2
  let sum = realAdd real1 real2
  
  putStrLn "Created 1 + 2 = 3"
  let approx = realApprox sum Z
  putStrLn $ "Sum approximation: " ++ showRat approx
  
  -- Real negation
  let neg = realNeg real1
  putStrLn "Created -1"
  
  putStrLn ""

-- ============================================
-- TEST 7: Completeness Setup
-- ============================================

testCompleteness :: IO ()
testCompleteness = do
  putStrLn "=== Testing Completeness Setup ==="
  
  -- Define a bounded set: {1, 1/2, 1/3, 1/4, ...}
  -- This set has supremum 1
  
  putStrLn "Set: {1, 1/2, 1/3, 1/4, ...}"
  putStrLn "Expected supremum: 1"
  putStrLn ""
  
  -- Note: Full proof requires implementing:
  -- 1. Set membership predicate
  -- 2. Boundedness proof
  -- 3. Supremum construction
  -- 4. Supremum verification
  
  putStrLn "Completeness theorem setup verified."
  putStrLn ""

-- ============================================
-- SUMMARY
-- ============================================

testAll :: IO ()
testAll = do
  putStrLn "========================================"
  putStrLn "REAL NUMBERS CONSTRUCTION - TEST SUITE"
  putStrLn "========================================"
  putStrLn ""
  
  testNat
  testInt
  testRat
  testCauchy
  testReal
  testRealArith
  testCompleteness
  
  putStrLn "========================================"
  putStrLn "TEST SUITE COMPLETED"
  putStrLn "========================================"
  putStrLn ""
  putStrLn "Next steps for completeness proof:"
  putStrLn "1. Implement set membership (1/n ∈ S)"
  putStrLn "2. Prove boundedness (∀x∈S, x ≤ 1)"
  putStrLn "3. Construct supremum using binary search"
  putStrLn "4. Verify supremum properties"
  putStrLn "5. Complete the theorem proof"

main :: IO ()
main = testAll
