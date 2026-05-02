-- ============================================
-- 依赖类型基础：相等、替换、同余
-- ============================================

-- 命题相等：Inductive family
data (=) : {a : Type} -> a -> a -> Type where
  Refl : {a : Type} -> {x : a} -> x = x

-- 替换原理（Leibniz 法则）
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

-- 同余原理
cong : {a : Type} -> {b : Type}
    -> (f : a -> b) -> {x : a} -> {y : a}
    -> x = y -> f x = f y
cong f {x} {y} prf = subst prf (\z => f x = f z) Refl

-- ============================================
-- 逻辑连接词
-- ============================================

-- 空类型（假）
data Void : Type where

-- 否定
Not : Type -> Type
Not A = A -> Void

-- 合取（使用 Sigma 类型）
And : Type -> Type -> Type
And A B = (a : A ** b : B)

-- 析取
data Or : Type -> Type -> Type where
  Inl : {a : Type} -> {b : Type} -> a -> Or a b
  Inr : {a : Type} -> {b : Type} -> b -> Or a b

-- 存在量词（Sigma 类型）
Exists : (A : Type) -> (A -> Type) -> Type
Exists A P = (x : A ** P x)

-- ============================================
-- 自然数与加法
-- ============================================

data Nat : Type where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add Z     m = m
add (S n) m = S (add n m)

-- 加法交换律（归纳证明）
addComm : (n : Nat) -> (m : Nat) -> add n m = add m n
addComm Z     m = Refl
addComm (S n) m = cong S (addComm n m)

-- 加法结合律（归纳证明）
addAssoc : (n : Nat) -> (m : Nat) -> (p : Nat)
         -> add n (add m p) = add (add n m) p
addAssoc Z     m p = Refl
addAssoc (S n) m p = cong S (addAssoc n m p)

-- ============================================
-- 有理数
-- 使用内置的 Rational（Integer :% Integer）
-- 假设已有 +, -, *, /, <, <= 运算
-- ============================================

-- 绝对值（通过 if-then-else 定义）
absRat : Rational -> Rational
absRat x = if x <= 0 then 0 - x else x

-- ============================================
-- Dedekind 分割定义实数
-- ============================================

-- 一个 Dedekind 分割由 "左集" L : Rational -> Type 刻画
-- 其余条件（非空、有界、开放）作为构造 Real 时的证明义务

data Real : Type where
  MkReal :
    (L : Rational -> Type) ->
    -- 左集非空
    (nonempty : Exists Rational L) ->
    -- 左集有上界
    (bounded : Exists Rational
      (\q => (r : Rational) -> L r -> r <= q)) ->
    -- 左集开放：若 q 属于左集，则存在更大的 r 也属于左集
    (open : (q : Rational) -> L q ->
      Exists Rational (\r => L r && q < r)) ->
    Real

-- 提取左集
lower : Real -> Rational -> Type
lower (MkReal L _ _ _) q = L q

-- ============================================
-- 实数的序关系
-- ============================================

-- x <= y 当且仅当 x 的左集包含于 y 的左集
RealLeq : Real -> Real -> Type
RealLeq x y = (q : Rational) -> lower x q -> lower y q

-- x < y 当且仅当 y 的左集包含不属于 x 的左集的元素
RealLt : Real -> Real -> Type
RealLt x y = Exists Rational
  (\q => Not (lower x q) && lower y q)

-- ============================================
-- 完备性定理：上确界存在
-- ============================================

-- 子集非空
Nonempty : (Real -> Type) -> Type
Nonempty S = Exists Real (\x => S x)

-- 子集有上界
BoundedAbove : (Real -> Type) -> Type
BoundedAbove S = Exists Real
  (\M => (x : Real) -> S x -> RealLeq x M)

-- M 是 S 的上确界：既是上界，又是最小的上界
IsSupremum : (Real -> Type) -> Real -> Type
IsSupremum S M =
  -- (1) M 是上界
  ((x : Real) -> S x -> RealLeq x M)
  &&
  -- (2) M 是最小的上界
  ((N : Real) ->
    ((x : Real) -> S x -> RealLeq x N) ->
    RealLeq M N)

-- ============================================
-- 核心定理：Dedekind 完备性
--
-- 定理陈述：每个非空且有上界的实数子集存在上确界。
--
-- 证明思路（构造性）：
-- 给定非空有上界集合 S，构造 sup S 如下：
--   (sup S).lower = { q : Rational | 存在 x ∈ S, q ∈ x.lower }
-- 即 sup S 的左集是 S 中所有元素左集的并。
--
-- 需要验证这个并集满足 Dedekind 分割的三个条件：
-- 1. 非空性：S 非空 => 存在 x ∈ S => x.lower 非空 => 并集非空
-- 2. 有界性：S 有上界 M => M.upper 非空 => 并集有上界
-- 3. 开放性：若 q ∈ 并集，则存在 x ∈ S 使 q ∈ x.lower
--    由 x 的开放性，存在 r ∈ x.lower 且 q < r，故 r ∈ 并集
-- ============================================

supremum :
  (S : Real -> Type) ->
  Nonempty S ->
  BoundedAbove S ->
  Exists Real (\M => IsSupremum S M)
supremum S nonEmpty bound =
  let
    -- sup S 的左集 = S 中所有元素左集的并
    supL : Rational -> Type
    supL q = Exists Real (\x => S x && lower x q)

    -- 非空性证明
    proofNonempty : Exists Rational supL
    proofNonempty =
      let (x ** xInS) = nonEmpty in
      let (MkReal Lx ne _ _) = x in
      let (q ** qInLx) = ne in
      (q ** (x ** (xInS && qInLx)))

    -- 有界性证明
    proofBounded : Exists Rational
      (\q => (r : Rational) -> supL r -> r <= q)
    proofBounded =
      let (M ** MIsBound) = bound in
      let (MkReal LM _ (q ** qBoundsL) _) = M in
      (q ** (\r => (\ev =>
        let (x ** (xInS && rInLx)) = ev in
        let rLeqM = MIsBound x xInS r rInLx in
        rLeqM)))

    -- 开放性证明
    proofOpen : (q : Rational) -> supL q ->
      Exists Rational (\r => supL r && q < r)
    proofOpen q ev =
      let (x ** (xInS && qInLx)) = ev in
      let (MkReal Lx _ _ openx) = x in
      let (r ** (rInLx && qLtR)) = openx q qInLx in
      (r ** ((x ** (xInS && rInLx)) && qLtR))

    -- 构造 sup S
    sup : Real
    sup = MkReal supL proofNonempty proofBounded proofOpen

    -- 证明 sup 是上界
    proofUpperBound :
      (x : Real) -> S x -> RealLeq x sup
    proofUpperBound x xInS q qInLx =
      (x ** (xInS && qInLx))

    -- 证明 sup 是最小上界
    proofLeast :
      (N : Real) ->
      ((x : Real) -> S x -> RealLeq x N) ->
      RealLeq sup N
    proofLeast N NIsBound q qInSup =
      let (x ** (xInS && qInLx)) = qInSup in
      let qInLN = NIsBound x xInS q qInLx in
      qInLN

  in
  (sup ** (proofUpperBound && proofLeast))
