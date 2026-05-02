-- Propositional equality tests
module Equality where

data (=) : {a : Type} -> a -> a -> Type where
  Refl : {a : Type} -> {x : a} -> x = x;

subst : {a : Type} -> {x : a} -> {y : a} -> x = y -> (P : a -> Type) -> P x -> P y;
subst Refl P px = px;

sym : {a : Type} -> {x : a} -> {y : a} -> x = y -> y = x;
sym {a} {x} {y} pf = subst pf (\z => z = x) Refl;

trans : {a : Type} -> {x : a} -> {y : a} -> {z : a} -> x = y -> y = z -> x = z;
trans {a} {x} {y} {z} p1 p2 = subst p2 (\w => x = w) p1;

cong : {a : Type} -> {b : Type} -> (f : a -> b) -> {x : a} -> {y : a} -> x = y -> f x = f y;
cong f Refl = Refl;

main = putStrLn "Equality test passed.";
