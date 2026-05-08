-- Simple test to verify the type checker works
module TestSimple where
import Base

data Nat = Z | S Nat

add : Nat -> Nat -> Nat
add Z y = y
add (S x) y = S (add x y)

main = putStrLn "Test passed"
