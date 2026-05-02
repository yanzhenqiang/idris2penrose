-- Simple functions and arithmetic
module Simple where

id : {a : Type} -> a -> a;
id x = x;

const : {a : Type} -> {b : Type} -> a -> b -> a;
const x y = x;

flip : {a : Type} -> {b : Type} -> {c : Type} -> (a -> b -> c) -> b -> a -> c;
flip f x y = f y x;

add : Int -> Int -> Int;
add x y = x + y;

main = putStrLn "Simple test passed.";
