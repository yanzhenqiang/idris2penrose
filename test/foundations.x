-- ============================================
-- 依赖类型基础引理演示
-- 包括相等类型的构造、替换、同余，以及加法交换律证明
-- ============================================

data Nat = Z | S Nat

add : Nat -> Nat -> Nat
add Z     m = m
add (S n) m = S (add n m)

-- 命题相等
data (=) : {a : Type} -> a -> a -> Type where
  Refl : {a : Type} -> {x : a} -> x = x

-- 替换原理
subst : {a : Type} -> {x : a} -> {y : a}
      -> x = y -> (P : a -> Type) -> P x -> P y
subst Refl P px = px

-- 对称性
sym : {a : Type} -> {x : a} -> {y : a} -> x = y -> y = x
sym {a} {x} {y} prf = subst prf (\z => z = x) Refl

-- 传递性
trans : {a : Type} -> {x : a} -> {y : a} -> {z : a}
      -> x = y -> y = z -> x = z
trans {a} {x} {y} {z} p1 p2 = subst p2 (\w => x = w) p1

-- 同余
cong : {a : Type} -> {b : Type}
    -> (f : a -> b) -> {x : a} -> {y : a}
    -> x = y -> f x = f y
cong f {x} {y} prf = subst prf (\z => f x = f z) Refl

-- 加法右单位元
addRZero : (n : Nat) -> add n Z = n
addRZero Z     = Refl
addRZero (S n) = cong S (addRZero n)

-- 加法右后继
addRSucc : (n : Nat) -> (m : Nat) -> add n (S m) = S (add n m)
addRSucc Z     m = Refl
addRSucc (S n) m = cong S (addRSucc n m)

-- 加法交换律（核心定理）
addComm : (n : Nat) -> (m : Nat) -> add n m = add m n
addComm Z     m = sym (addRZero m)
addComm (S n) m = trans
  (cong S (addComm n m))
  (sym (addRSucc m n))

-- 加法结合律
addAssoc : (n : Nat) -> (m : Nat) -> (p : Nat)
         -> add n (add m p) = add (add n m) p
addAssoc Z     m p = Refl
addAssoc (S n) m p = cong S (addAssoc n m p)

main = putStrLn "Foundations of dependent type theory verified."
