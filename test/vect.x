-- Length-indexed vectors (dependent types)
module VectTest where

data Nat = Z | S Nat;

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a;
  Cons : (n : Nat) -> a -> Vect n a -> Vect (S n) a;

head : (n : Nat) -> (a : Type) -> Vect (S n) a -> a;
head n a (Cons _ x _) = x;

tail : (n : Nat) -> (a : Type) -> Vect (S n) a -> Vect n a;
tail n a (Cons _ _ xs) = xs;

append : (n : Nat) -> (m : Nat) -> (a : Type) -> Vect n a -> Vect m a -> Vect (add n m) a;
append Z m a Nil ys = ys;
append (S n) m a (Cons _ x xs) ys = Cons (add n m) x (append n m a xs ys);

add : Nat -> Nat -> Nat;
add Z y = y;
add (S x) y = S (add x y);

main = putStrLn "Vect test passed.";
