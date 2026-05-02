-- Natural numbers and addition
module NatTest where

data Nat = Z | S Nat;

add : Nat -> Nat -> Nat;
add Z y = y;
add (S x) y = S (add x y);

mul : Nat -> Nat -> Nat;
mul Z _ = Z;
mul (S x) y = add y (mul x y);

fact : Nat -> Nat;
fact Z = S Z;
fact (S n) = mul (S n) (fact n);

main = putStrLn "Nat test passed.";
