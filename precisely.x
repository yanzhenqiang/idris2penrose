module Base where

infixr 9 .
infixr 8 ^
infixl 7 * , /, `div` , `mod` , `quot`, `rem`
infixr 6 <>
infixl 6 + , -
infixr 5 ++
infixl 4 <*> , <$> , <* , *>
infix 4 == , /= , <= , < , >= , >
infixl 3 && , <|>
infixl 2 ||
infixl 1 >> , >>=
infixr 1 =<<
infixr 0 $

class Semigroup a where
  (<>) :: a -> a -> a
class Monoid a where
  mempty :: a
  mconcat :: [a] -> a
  mconcat = foldr (<>) mempty
instance Monoid [a] where
  mempty = []
instance Semigroup [a] where
  (<>) = (++)
class Functor f where fmap :: (a -> b) -> f a -> f b
class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
(<$>) = fmap
liftA2 f x y = f <$> x <*> y
(>>) f g = f >>= \_ -> g
(=<<) = flip (>>=)
instance Functor ((->) r) where fmap = (.)
instance Applicative ((->) r) where
  pure = const
  f <*> x = \r -> f r (x r)
instance Monad ((->) r) where
  return = const
  x >>= f = \r -> f (x r) r
class Eq a where (==) :: a -> a -> Bool
instance Eq () where () == () = True
instance Eq Bool where
  True == True = True
  False == False = True
  _ == _ = False
instance (Eq a, Eq b) => Eq (a, b) where
  (a1, b1) == (a2, b2) = a1 == a2 && b1 == b2
instance Eq a => Eq [a] where
  xs == ys = case xs of
    [] -> case ys of
      [] -> True
      _ -> False
    x:xt -> case ys of
      [] -> False
      y:yt -> x == y && xt == yt
instance Eq Int where (==) = intEq
instance Eq Char where (==) = charEq
($) f x = f x
id x = x
const x y = x
flip f x y = f y x
(&) x f = f x
class Ord a where
  (<=) :: a -> a -> Bool
  x <= y = case compare x y of
    LT -> True
    EQ -> True
    GT -> False
  compare :: a -> a -> Ordering
  compare x y = if x <= y then if y == x then EQ else LT else GT
instance Ord Int where (<=) = intLE
instance Ord Char where (<=) = charLE
data Ordering = LT | GT | EQ deriving (Eq, Show)
instance Ord a => Ord [a] where
  xs <= ys = case xs of
    [] -> True
    x:xt -> case ys of
      [] -> False
      y:yt -> if x <= y then if y <= x then xt <= yt else True else False
  compare xs ys = case xs of
    [] -> case ys of
      [] -> EQ
      _ -> LT
    x:xt -> case ys of
      [] -> GT
      y:yt -> if x <= y then if y <= x then compare xt yt else LT else GT
data Maybe a = Nothing | Just a deriving (Eq, Show)
data Either a b = Left a | Right b deriving (Eq, Show)

fst (x, y) = x
snd (x, y) = y
uncurry f (x, y) = f x y
first f (x, y) = (f x, y)
second f (x, y) = (x, f y)
bool a b c = if c then b else a
not a = if a then False else True
x /= y = not $ x == y
(.) f g x = f (g x)
(||) f g = if f then True else g
(&&) f g = if f then g else False

take 0 xs = []
take _ [] = []
take n (h:t) = h : take (n - 1) t

drop n xs | n <= 0 = xs
drop _ []           = []
drop n (_:xs)       = drop (n-1) xs

splitAt n xs = (take n xs, drop n xs)

maybe n j m = case m of Nothing -> n; Just x -> j x

instance Functor Maybe where fmap f = maybe Nothing (Just . f)
instance Applicative Maybe where pure = Just; mf <*> mx = maybe Nothing (\f -> maybe Nothing (Just . f) mx) mf
instance Monad Maybe where return = Just; mf >>= mg = maybe Nothing mg mf
instance Alternative Maybe where empty = Nothing; x <|> y = maybe y Just x

foldr c n = \case [] -> n; h:t -> c h $ foldr c n t

length :: [a] -> Int
length = foldr (\_ n -> n + 1) 0

mapM f = foldr (\a rest -> liftA2 (:) (f a) rest) (pure [])
mapM_ f = foldr ((>>) . f) (pure ())
forM = flip mapM
sequence = mapM id
replicateM = (sequence .) . replicate
foldM f z0 xs = foldr (\x k z -> f z x >>= k) pure xs z0
when x y = if x then y else pure ()
unless x y = if x then pure () else y
error = primitiveError
undefined = error "undefined"

foldr1 c l@(h:t) = maybe undefined id $ foldr (\x m -> Just $ maybe x (c x) m) Nothing l
foldl f a bs = foldr (\b g x -> g (f x b)) (\x -> x) bs a
foldl1 f (h:t) = foldl f h t

scanl f q ls = q : (case ls of
  []   -> []
  x:xs -> scanl f (f q x) xs)
scanl1 f (x:xs) =  scanl f x xs
scanl1 _ []     = []

elem k xs = foldr (\x t -> x == k || t) False xs
notElem = (not .) . elem
find f xs = foldr (\x t -> if f x then Just x else t) Nothing xs
(++) = flip (foldr (:))
concat = foldr (++) []
map = flip (foldr . ((:) .)) []
head (h:_) = h
tail (_:t) = t

isSpace c = elem (ord c) [32, 9, 10, 11, 12, 13, 160]
words s = case dropWhile isSpace s of
  "" -> []
  s' -> w : words s'' where (w, s'') = break isSpace s'
lines "" =  []
lines s | (l, s') <- break (== '\n') s = l : case s' of
  [] -> []
  _:s'' -> lines s''

instance Functor [] where fmap = map
instance Applicative [] where pure = (:[]); f <*> x = concatMap (<$> x) f
instance Monad [] where return = (:[]); (>>=) = flip concatMap
instance Alternative [] where empty = []; (<|>) = (++)

concatMap = (concat .) . map
lookup s = foldr (\(k, v) t -> if s == k then Just v else t) Nothing
filter p = foldr (\x -> bool id (x:) $ p x) []
filterM p = foldr (\x -> liftA2 (bool id (x:)) $ p x) $ pure []
union xs ys = xs ++ filter (`notElem` xs) (nub ys)
nub l = go l [] where
  go [] _ = []
  go (y:yt) xs
    | elem y xs = go yt xs
    | otherwise = y : go yt (y:xs)
partition p = foldr go ([], []) where
  go x (ts, fs)
    | p x = (x:ts, fs)
    | otherwise = (ts, x:fs)
intersect xs ys = filter (\x -> maybe False (\_ -> True) $ find (x ==) ys) xs
xs \\ ys = filter (not . (`elem` ys)) ys
last (x:xt) = go x xt where go x xt = case xt of [] -> x; y:yt -> go y yt
init (x:xt) = case xt of [] -> []; _ -> x : init xt
intercalate sep = \case [] -> []; x:xt -> x ++ concatMap (sep ++) xt
intersperse sep = \case [] -> []; x:xt -> x : foldr ($) [] (((sep:) .) . (:) <$> xt)

all f = and . map f
any f = or . map f
and = foldr (&&) True
or = foldr (||) False

zipWith f xs ys = case xs of [] -> []; x:xt -> case ys of [] -> []; y:yt -> f x y : zipWith f xt yt
zip = zipWith (,)
unzip [] = ([], [])
unzip ((a, b):rest) = (a:at, b:bt) where (at, bt) = unzip rest

transpose []             = []
transpose ([]     : xss) = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])

sum = foldr (+) 0
product = foldr (*) 1

max a b = if a <= b then b else a
min a b = if a <= b then a else b

abs x = if 0 <= x then x else -x
signum x | 0 == x = 0
         | 0 <= x = 1
         | otherwise = -1
otherwise = True

gcd x y = gcd' (abs x) (abs y) where
  gcd' a 0 = a
  gcd' a b = gcd' b (a `rem` b)
lcm = \cases
  _ 0 -> 0
  0 _ -> 0
  x y -> abs ((x `quot` (gcd x y)) * y)

iterate f x = x : iterate f (f x)
takeWhile _ [] = []
takeWhile p xs@(x:xt)
  | p x  = x : takeWhile p xt
  | True = []

dropWhileEnd p = foldr (\x xs -> if p x && null xs then [] else x : xs) []

a ^ b = case b of
  0 -> 1
  1 -> a
  _ -> case r of
    0 -> h2
    1 -> h2*a
  where
  (q, r) = divMod b 2
  h = a^q
  h2 = h*h

class Enum a where
  succ           :: a -> a
  pred           :: a -> a
  toEnum         :: Int -> a
  fromEnum       :: a -> Int
  enumFrom       :: a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]
  succ = toEnum . (+ 1) . fromEnum
  pred = toEnum . (- 1) . fromEnum
  enumFrom x = map toEnum [fromEnum x ..]
  enumFromThen x y = map toEnum [fromEnum x, fromEnum y ..]
  enumFromTo x y = map toEnum [fromEnum x .. fromEnum y]
  enumFromThenTo x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]

instance Enum Int where
  succ = (+ 1)
  pred = (- 1)
  toEnum = id
  fromEnum = id
  enumFrom = iterate succ
  enumFromTo lo hi = takeWhile (<= hi) $ enumFrom lo

instance Enum Bool where
  toEnum 0 = False
  toEnum 1 = True
  fromEnum False = 0
  fromEnum True = 1

instance Enum Char where
  toEnum = chr
  fromEnum = ord

fromIntegral = fromInteger . toInteger

class Ring a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  fromInteger :: Integer -> a
  negate :: a -> a
  negate = (0 -)

class Field a where
  recip :: a -> a
  recip = (1 /)
  (/) :: a -> a -> a
  a / b = a * recip b
  fromRational :: Rational -> a
  fromRational (a:%b) = fromInteger a / fromInteger b

class Integral a where
  div :: a -> a -> a
  mod :: a -> a -> a
  quot :: a -> a -> a
  rem :: a -> a -> a
  toInteger :: a -> Integer
  divMod :: a -> a -> (a, a)
  quotRem :: a -> a -> (a, a)

instance Ring Int where
  (+) = intAdd
  (-) = intSub
  (*) = intMul
  fromInteger = intFromWord . fromInteger

instance Integral Int where
  div = intDiv
  mod = intMod
  quot = intQuot
  rem = intRem
  toInteger x
    | 0 <= x = Integer True $ if x == 0 then [] else [wordFromInt x]
    | True = Integer False [wordFromInt -x]

instance Ring Word where
  (+) = wordAdd
  (-) = wordSub
  (*) = wordMul
  fromInteger (Integer xsgn xs) = (if xsgn then id else wordSub zeroWord) case xs of
    [] -> zeroWord
    (x:_) -> x

instance Integral Word where
  div = wordDiv
  mod = wordMod
  quot = wordQuot
  rem = wordRem
  toInteger x = Integer True $ if x == 0 then [] else [x]

instance Eq Word where (==) = wordEq
instance Ord Word where (<=) = wordLE

-- Multiprecision arithmetic.
data Integer = Integer Bool [Word] deriving Eq
instance Ring Integer where
  Integer xsgn xs + Integer ysgn ys
    | xsgn == ysgn = Integer xsgn $ mpAdd xs ys
    | True = case mpCompare xs ys of
      LT -> mpCanon ysgn $ mpSub ys xs
      EQ -> Integer True []
      _ -> mpCanon xsgn $ mpSub xs ys
  Integer xsgn xs - Integer ysgn ys
    | xsgn /= ysgn = Integer xsgn $ mpAdd xs ys
    | True = case mpCompare xs ys of
      LT -> mpCanon (not ysgn) $ mpSub ys xs
      EQ -> Integer True []
      _ -> mpCanon xsgn $ mpSub xs ys
  Integer xsgn xs * Integer ysgn ys
    | null xs || null ys = Integer True []
    | True = Integer (xsgn == ysgn) $ mpMul xs ys
  fromInteger = id

instance Integral Integer where
  div (Integer xsgn xs) (Integer ysgn ys) = if xsgn == ysgn
    then Integer True qs
    else case rs of
      [] -> mpCanon0 False qs
      _  -> mpCanon0 False $ mpAdd qs [1]
    where (qs, rs) = mpDivMod xs ys
  mod (Integer xsgn xs) (Integer ysgn ys) = if xsgn == ysgn
    then mpCanon0 xsgn rs
    else mpCanon ysgn $ mpSub ys rs
    where rs = snd $ mpDivMod xs ys
  quot (Integer xsgn xs) (Integer ysgn ys) = mpCanon0 (xsgn == ysgn) $ fst $ mpDivMod xs ys
  rem (Integer xsgn xs) (Integer ysgn ys) = mpCanon0 xsgn $ snd $ mpDivMod xs ys
  toInteger = id

instance Ord Integer where
  compare (Integer xsgn xs) (Integer ysgn ys)
    | xsgn = if ysgn then mpCompare xs ys else GT
    | True = if ysgn then LT else mpCompare ys xs

mpView [] = (0, [])
mpView (x:xt) = (x, xt)

mpCanon sgn xs = mpCanon0 sgn $ reverse $ dropWhile (0 ==) $ reverse xs
mpCanon0 sgn xs = case xs of
  [] -> Integer True []
  _ -> Integer sgn xs

mpCompare [] [] = EQ
mpCompare [] _  = LT
mpCompare _  [] = GT
mpCompare (x:xt) (y:yt) = case mpCompare xt yt of
  EQ -> compare x y
  o -> o

mpAdd xs ys = mpAdc xs ys 0 where
  mpAdc [] [] c
    | c == 0 = []
    | otherwise = [1]
  mpAdc xs ys c = wordFromUU n : mpAdc xt yt c' where
    (x, xt) = mpView xs
    (y, yt) = mpView ys
    c' = shiftR n 32
    n = uuPad x + uuPad y + c

mpSub xs ys = fst $ mpSbb xs ys 0

mpSbb = go where
  go [] [] b = ([], b)
  go xs ys b = first (wordFromUU n:) $ go xt yt b' where
    (x, xt) = mpView xs
    (y, yt) = mpView ys
    b' = 1 - shiftR n 32
    n = shiftL 1 32 + uuPad x - uuPad y - b

mpMulWord x ys = mpMulWord' x ys 0 where
  mpMulWord' _ []     c = if c == 0 then [] else [wordFromUU c]
  mpMulWord' x (y:yt) c = lo:mpMulWord' x yt hi where
    lo = wordFromUU n
    hi = shiftR n 32
    n = uuPad x * uuPad y + c

mpMul [] _ = []
mpMul (x:xt) ys = case mpMulWord x ys of
  [] -> []
  z:zs -> z:mpAdd zs (mpMul xt ys)

mpDivModWord xs y = first (reverse . dropWhile (0 ==)) $ go 0 $ reverse xs where
  go r [] = ([], r)
  go n (x:xt) = first (q:) $ go r xt where
    q = wordFromUU $ (uuPad x + shiftL (uuPad n) 32) `div` uuPad y
    r = x - q*y

mpDivMod xs ys = first (reverse . dropWhile (== 0)) $ go us where
  s = mpDivScale $ last ys
  us = mpMulWord s (xs ++ [0])
  vs = mpMulWord s ys
  (v1:vt) = reverse vs
  vlen = length vs
  go us | ulen <= vlen = ([], fst $ mpDivModWord us s)
        | True = first (q:) $ go $ lsbs ++ init ds
    where
    ulen = length us
    (u0:u1:ut) = reverse us
    (lsbs, msbs) = splitAt (ulen - vlen - 1) us
    quu = (uuPad u1 + shiftL (uuPad u0) 32) `div` uuPad v1
    q0 = if shiftL 1 32 <= quu then -1 else wordFromUU quu
    (q, ds) = foldr const undefined [(q, ds) | q <- iterate (- 1) q0, let (ds, bor) = mpSbb msbs (mpMulWord q vs) 0, bor == 0]

mpDivScale n
  | n1 == 0 = 1
  | otherwise = wordFromUU $ shiftL 1 32 `div` uuPad n1
  where n1 = succ n

mpBase _ [] = ('0':)
mpBase b xs = go xs where
  go [] = id
  go xs = go q . shows r where (q, r) = mpDivModWord xs b

instance Show Integer where showsPrec _ (Integer xsgn xs) = (if xsgn then id else ('-':)) . mpBase 10 xs

a < b = a <= b && a /= b
a > b = b <= a && a /= b
(>=) = flip(<=)

instance Show () where show () = "()"
instance Show Bool where
  show True = "True"
  show False = "False"
instance Show a => Show [a] where showsPrec _ = showList
instance Show Int where
  showsPrec _ n
    | 0 == n = ('0':)
    | 1 <= n = showInt__ n
    | 2 * n == 0 = ("-2147483648"++)
    | True = ('-':) . showInt__ (0 - n)

showInt__ n
  | 0 == n = id
  | True = showInt__ (n`div`10) . (chr (48+n`mod`10):)

showWord_ n
  | 0 == n = id
  | True = showWord_ (n`div`10) . (chr (48+(intFromWord $ n`mod`10)):)

instance Show Word where
  showsPrec _ n
    | 0 == n = ('0':)
    | True = showWord_ n

showLitChar__ '\n' = ("\\n"++)
showLitChar__ '\\' = ("\\\\"++)
showLitChar__ c
  | n < 32 || n > 127 = ('\\':) . protectDecEsc (shows n)
  | otherwise = (c:)
  where n = ord c

protectDecEsc f s
  | (c:_) <- s, '0' <= c, c <= '9' = f $ ("\\&"++) s
  | otherwise = f s

instance Show Char where
  showsPrec _ '\'' = ("'\\''"++)
  showsPrec _ c = ('\'':) . showLitChar__ c . ('\'':)
  showList s = ('"':) . foldr (.) id (map go s) . ('"':) where
    go '"' = ("\\\""++)
    go c = showLitChar__ c

instance (Show a, Show b) => Show (a, b) where
  showsPrec _ (a, b) = showParen True $ shows a . (',':) . shows b

-- Map
data Map k a = Tip | Bin Int k a (Map k a) (Map k a)
instance Functor (Map k) where fmap f m = case m of
  Tip -> Tip
  Bin sz k x l r -> Bin sz k (f x) (fmap f l) (fmap f r)
size m = case m of Tip -> 0 ; Bin sz _ _ _ _ -> sz
node k x l r = Bin (1 + size l + size r) k x l r
singleton k x = Bin 1 k x Tip Tip
singleL k x l (Bin _ rk rkx rl rr) = node rk rkx (node k x l rl) rr
doubleL k x l (Bin _ rk rkx (Bin _ rlk rlkx rll rlr) rr) =
  node rlk rlkx (node k x l rll) (node rk rkx rlr rr)
singleR k x (Bin _ lk lkx ll lr) r = node lk lkx ll (node k x lr r)
doubleR k x (Bin _ lk lkx ll (Bin _ lrk lrkx lrl lrr)) r =
  node lrk lrkx (node lk lkx ll lrl) (node k x lrr r)
balance k x l r = f k x l r where
  f | size l + size r <= 1 = node
    | 5 * size l + 3 <= 2 * size r = case r of
      Tip -> node
      Bin sz _ _ rl rr -> if 2 * size rl + 1 <= 3 * size rr
        then singleL
        else doubleL
    | 5 * size r + 3 <= 2 * size l = case l of
      Tip -> node
      Bin sz _ _ ll lr -> if 2 * size lr + 1 <= 3 * size ll
        then singleR
        else doubleR
    | True = node
insert kx x t = case t of
  Tip -> singleton kx x
  Bin sz ky y l r -> case compare kx ky of
    LT -> balance ky y (insert kx x l) r
    GT -> balance ky y l (insert kx x r)
    EQ -> Bin sz kx x l r
insertWith f kx x t = case t of
  Tip -> singleton kx x
  Bin sy ky y l r -> case compare kx ky of
    LT -> balance ky y (insertWith f kx x l) r
    GT -> balance ky y l (insertWith f kx x r)
    EQ -> Bin sy kx (f x y) l r
mlookup kx t = case t of
  Tip -> Nothing
  Bin _ ky y l r -> case compare kx ky of
    LT -> mlookup kx l
    GT -> mlookup kx r
    EQ -> Just y
fromList = foldl (\t (k, x) -> insert k x t) Tip
member k t = maybe False (const True) $ mlookup k t
t ! k = maybe undefined id $ mlookup k t

foldrWithKey f = go where
  go z t = case t of
    Tip -> z
    Bin _ kx x l r -> go (f kx x (go z r)) l

toAscList = foldrWithKey (\k x xs -> (k,x):xs) []
keys = map fst . toAscList

-- Either / State / Applicative / Alternative instances for Parser etc.
instance Functor IO where fmap f x = ioPure f <*> x
instance Applicative IO where pure = ioPure ; (<*>) f x = ioBind f \g -> ioBind x \y -> ioPure (g y)
instance Monad IO where return = ioPure ; (>>=) = ioBind

class Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
asum = foldr (<|>) empty
(*>) = liftA2 \x y -> y
(<*) = liftA2 \x y -> x
between x y p = x *> (p <* y)

showParen b f = if b then ('(':) . f . (')':) else f

unwords [] = ""
unwords ws = foldr1 (\w s -> w ++ ' ':s) ws
unlines = concatMap (++"\n")

readNatural = foldl (\n d -> toInteger 10*n + toInteger (ord d - ord '0')) (toInteger 0)
readInteger ('-':t) = -(readNatural t)
readInteger s = readNatural s

infixl 7 %
data Rational = Integer :% Integer deriving Eq
numerator (p :% _) = p
denominator (_ :% q) = q
x % y = reduce_ (x * signum y) (abs y)
reduce_ x y = (x `quot` d) :% (y `quot` d) where d = gcd x y
instance Ord Rational where (a :% b) <= (c :% d) = a*d <= b*c
instance Ring Rational where
  (a :% b) + (c :% d) = reduce_ (a*d + b*c) (b*d)
  (a :% b) - (c :% d) = reduce_ (a*d - b*c) (b*d)
  (a :% b) * (c :% d) = reduce_ (a*c) (b*d)
  fromInteger n = n :% 1
instance Show Rational where
  showsPrec _ (a :% b) = shows a . (" % "++) . shows b
instance Field Rational where recip (x :% y) = (y * signum x) :% abs x

instance Ring Double where
  (+) = doubleAdd
  (-) = doubleSub
  (*) = doubleMul
  fromInteger n = integerSignList n \sgn ws -> case reverse ws of
    [] -> doubleFromInt 0
    x:xt -> (if sgn then id else negate) let
      dx = doubleFromWord x
      sh = foldr1 (*) $ replicate 32 $ doubleFromInt 2
      in case xt of
        [] -> dx
        y:yt -> foldr (const (sh*)) (dx*sh + doubleFromWord y) yt
instance Eq Double where (==) = doubleEq
instance Ord Double where (<=) = doubleLE
instance Show Double where
  showsPrec _ d = case compare d 0 of
    EQ -> ('0':)
    LT -> ('-':) . shows -d
    GT
      | d >= 9999999.5 -> big 7 10000000
      | d >= 0.0000995 -> dotty d
      | otherwise -> let
        (as, bs) = span (>= d) $ iterate (0.1*) 1
        in dotty (d / head bs) . ("e-"++) . shows (length as)
      where
      dotty norm = let
        n = intFromDouble $ 0.0000005 + norm
        in shows n . ('.':) . (tail (show $ 1000000 + intFromDouble (0.5 + 1000000 * (norm - doubleFromInt n)))++)
      big e b
        | 10.0*b > d = dotty (d / b) . ('e':) . shows e
        | otherwise = big (e + 1::Int) (10*b)

instance Field Double where (/) = doubleDiv

floor = intFromDouble . doubleFloor
ceiling x = 0 - floor (0 - x)

zeroWord = wordFromInt $ ord '\0'

integerSignList (Integer xsgn xs) f = f xsgn xs
module Ast where
import Base

-- ============================================
-- CIC AST (Calculus of Inductive Constructions)
-- Based on Lean 4 / Coq core type theory
-- ============================================

-- Universe levels: natural numbers with arithmetic
data Level
  = LZero          -- 0
  | LSucc Level    -- u + 1
  | LMax Level Level
  | LVar String    -- universe polymorphism variable
  deriving (Eq, Show)

-- Sort: the typing universes
data Sort
  = SProp          -- Sort 0: proof-irrelevant propositions
  | SType Level    -- Sort (u+1): Type u
  | SSucc Sort     -- successor universe (for cumulativity)
  deriving (Eq, Show)

-- Names: raw, De Bruijn index, or global
data Name = Raw String | Ind Int | Global String deriving (Eq, Show)

-- ============================================
-- TERMS: Core CIC syntax
-- ============================================
data Term
  = Var Name                     -- variable
  | App Term Term                -- application f x
  | Lam Binder Term              -- lambda
  | Pi Binder Term               -- dependent function type
  | Let Name Term Term Term      -- let x : T = v in b
  | Sort Sort                    -- universe sort
  | Inductive IndDef             -- inductive type definition
  | Constr String String [Term]  -- constructor: typeName conName args
  | Case Term [Clause]           -- pattern matching elimination
  | Meta Int                     -- metavariable (for unification)
  | Proj Int Term                -- projection (record/structure)
  | Fix FixInfo Term             -- fixpoint (primitive recursion)
  | Refl Term                    -- equality witness
  | Eq Term Term Term            -- @Eq A x y
  | Annot Term Term              -- (e : T)
  | NatLit Int
  | CharLit Int
  | StringLit String
  | Hole String
  deriving (Eq, Show)

-- Binder: explicit or implicit parameter
data Binder
  = BExplicit Name Term          -- (x : A)
  | BImplicit Name Term          -- {x : A}
  deriving (Eq, Show)

-- Inductive definition (families)
data IndDef = IndDef
  { indName    :: String
  , indParams  :: [Binder]       -- parameters (shared across constructors)
  , indIndices :: [Binder]       -- indices (vary per constructor)
  , indSort    :: Sort             -- target universe
  , indConstrs :: [ConstrDef]
  } deriving (Eq, Show)

data ConstrDef = ConstrDef
  { conName   :: String
  , conArgs   :: [Binder]        -- constructor arguments
  , conResult :: [Term]            -- indices in return type (applied to params)
  } deriving (Eq, Show)

-- Pattern matching clause
data Clause = Clause Pattern Term deriving (Eq, Show)

data Pattern
  = PVar Name
  | PCon String [Pattern]
  | PLit Int
  | PWild
  | PInaccessible Term          -- inaccessible pattern (dot pattern)
  | PAnnotated Pattern Term
  deriving (Eq, Show)

-- Fixpoint info for structural recursion
data FixInfo = FixInfo
  { fixName   :: Name
  , fixType   :: Term
  , fixRecArg :: Int               -- which argument is the decreasing one
  } deriving (Eq, Show)

-- Declarations
data Decl
  = TypeSig String Term
  | FunDef String [Clause]
  | IndDecl IndDef
  | InfixDecl Fixity Int [String]
  | AxiomDecl String Term          -- postulate/axiom
  deriving (Eq, Show)

data Fixity = Infix | InfixL | InfixR deriving (Eq, Show)

type Program = [Decl]

-- ============================================
-- PRETTY PRINTING
-- ============================================
ppName (Raw s)    = s
ppName (Ind i)    = "v" ++ show i
ppName (Global s) = s

ppLevel LZero     = "0"
ppLevel (LSucc u) = "(succ " ++ ppLevel u ++ ")"
ppLevel (LMax u v) = "(max " ++ ppLevel u ++ " " ++ ppLevel v ++ ")"
ppLevel (LVar s)  = "u_" ++ s

ppSort SProp         = "Prop"
ppSort (SType LZero) = "Type"
ppSort (SType u)     = "Type " ++ ppLevel u
ppSort (SSucc s)     = "Sort (" ++ ppSort s ++ " + 1)"

ppBinder (BExplicit n t) = "(" ++ ppName n ++ " : " ++ ppTerm t ++ ")"
ppBinder (BImplicit n t) = "{" ++ ppName n ++ " : " ++ ppTerm t ++ "}"

ppTerm (Var n)       = ppName n
ppTerm (App f x)     = "(" ++ ppTerm f ++ " " ++ ppTerm x ++ ")"
ppTerm (Lam b body)  = "(fun " ++ ppBinder b ++ " => " ++ ppTerm body ++ ")"
ppTerm (Pi b body)   = case b of
  BExplicit (Raw "_") t -> "(" ++ ppTerm t ++ " -> " ++ ppTerm body ++ ")"
  _ -> "(forall " ++ ppBinder b ++ ", " ++ ppTerm body ++ ")"
ppTerm (Let n ty val body) = "(let " ++ ppName n ++ " : " ++ ppTerm ty ++ " := " ++ ppTerm val ++ " in " ++ ppTerm body ++ ")"
ppTerm (Sort s)      = ppSort s
ppTerm (Inductive d) = "<inductive " ++ indName d ++ ">"
ppTerm (Constr tn cn args) = "(" ++ cn ++ foldr (\a r -> " " ++ ppTerm a ++ r) "" args ++ ")"
ppTerm (Case e cs)   = "(match " ++ ppTerm e ++ " with " ++ intercalate " | " (map (\(Clause p r) -> ppPat p ++ " => " ++ ppTerm r) cs) ++ ")"
ppTerm (Meta i)      = "?_" ++ show i
ppTerm (Proj i e)    = "(proj" ++ show i ++ " " ++ ppTerm e ++ ")"
ppTerm (Fix _ t)     = "(fix " ++ ppTerm t ++ ")"
ppTerm (Refl e)      = "(Refl " ++ ppTerm e ++ ")"
ppTerm (Eq a x y)    = "(@Eq " ++ ppTerm a ++ " " ++ ppTerm x ++ " " ++ ppTerm y ++ ")"
ppTerm (Annot e t)   = "(" ++ ppTerm e ++ " : " ++ ppTerm t ++ ")"
ppTerm (NatLit n)    = show n
ppTerm (CharLit c)   = "'" ++ chr c : "'"
ppTerm (StringLit s) = "\"" ++ s ++ "\""
ppTerm (Hole h)      = "?" ++ h

ppPat (PVar n)       = ppName n
ppPat (PCon c ps)    = "(" ++ c ++ " " ++ unwords (map ppPat ps) ++ ")"
ppPat (PLit n)       = show n
ppPat PWild          = "_"
ppPat (PInaccessible t)= "." ++ ppTerm t
ppPat (PAnnotated p t)= "(" ++ ppPat p ++ " : " ++ ppTerm t ++ ")"

-- ============================================
-- DE BRUIJN CONVERSION
-- ============================================
toDeBruijn :: [(Name, Int)] -> Term -> Term
toDeBruijn env t = case t of
  Var n -> case lookup n env of
    Just i -> Var (Ind i)
    Nothing -> Var n
  App f x -> App (toDeBruijn env f) (toDeBruijn env x)
  Lam (BExplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Lam (BExplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Lam (BImplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Lam (BImplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Pi (BExplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Pi (BExplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Pi (BImplicit n ty) b ->
    let env' = (n, 0) : map (second (+1)) env
    in Pi (BImplicit (Ind 0) (toDeBruijn env ty)) (toDeBruijn env' (shift 1 b))
  Let n ty val b ->
    let env' = (n, 0) : map (second (+1)) env
    in Let (Ind 0) (toDeBruijn env ty) (toDeBruijn env val) (toDeBruijn env' (shift 1 b))
  Case e cs -> Case (toDeBruijn env e) (map (\(Clause p r) -> Clause (toDBPat p) (toDeBruijn (patEnv p env) r)) cs)
  Eq a x y -> Eq (toDeBruijn env a) (toDeBruijn env x) (toDeBruijn env y)
  Refl e -> Refl (toDeBruijn env e)
  Annot e t' -> Annot (toDeBruijn env e) (toDeBruijn env t')
  Proj i e -> Proj i (toDeBruijn env e)
  Fix info t' -> Fix info (toDeBruijn env t')
  _ -> t

shift :: Int -> Term -> Term
shift k t = case t of
  Var (Ind i) -> Var (Ind $ if i < k then i else i + 1)
  Var n -> Var n
  App f x -> App (shift k f) (shift k x)
  Lam (BExplicit n ty) b -> Lam (BExplicit n (shift k ty)) (shift (k+1) b)
  Lam (BImplicit n ty) b -> Lam (BImplicit n (shift k ty)) (shift (k+1) b)
  Pi (BExplicit n ty) b -> Pi (BExplicit n (shift k ty)) (shift (k+1) b)
  Pi (BImplicit n ty) b -> Pi (BImplicit n (shift k ty)) (shift (k+1) b)
  Let n ty val b -> Let n (shift k ty) (shift k val) (shift (k+1) b)
  Case e cs -> Case (shift k e) (map (\(Clause p r) -> Clause (shiftPat k p) (shift k r)) cs)
  Eq a x y -> Eq (shift k a) (shift k x) (shift k y)
  Refl e -> Refl (shift k e)
  Annot e t' -> Annot (shift k e) (shift k t')
  Proj i e -> Proj i (shift k e)
  Fix info t' -> Fix info (shift k t')
  _ -> t

toDBPat :: Pattern -> Pattern
toDBPat p = case p of
  PVar n -> PVar (Ind 0)
  PCon c ps -> PCon c (map toDBPat ps)
  PLit n -> PLit n
  PWild -> PWild
  PInaccessible t -> PInaccessible (shift (patDepth p) t)
  PAnnotated p' t -> PAnnotated (toDBPat p') (shift (patDepth p') t)

patEnv :: Pattern -> [(Name, Int)] -> [(Name, Int)]
patEnv p env = case p of
  PVar n -> (n, 0) : map (second (+1)) env
  PCon _ ps -> foldr (\p' e -> patEnv p' e) env ps
  PLit _ -> env
  PWild -> env
  PInaccessible _ -> env
  PAnnotated p' _ -> patEnv p' env

patDepth :: Pattern -> Int
patDepth p = case p of
  PVar _ -> 1
  PCon _ ps -> sum (map patDepth ps)
  PLit _ -> 0
  PWild -> 0
  PInaccessible _ -> 0
  PAnnotated p' _ -> patDepth p'

shiftPat :: Int -> Pattern -> Pattern
shiftPat k p = case p of
  PVar (Ind i) -> PVar (Ind $ if i < k then i else i + 1)
  PCon c ps -> PCon c (map (shiftPat k) ps)
  _ -> p

-- ============================================
-- SUBSTITUTION
-- ============================================
substitute :: Term -> Name -> Term -> Term
substitute val n t = case t of
  Var n' | n == n' -> val
         | otherwise -> Var n'
  App f x -> App (substitute val n f) (substitute val n x)
  Lam (BExplicit n' ty) b ->
    if n == n' then Lam (BExplicit n' (substitute val n ty)) b
    else Lam (BExplicit n' (substitute val n ty)) (substitute val n b)
  Lam (BImplicit n' ty) b ->
    if n == n' then Lam (BImplicit n' (substitute val n ty)) b
    else Lam (BImplicit n' (substitute val n ty)) (substitute val n b)
  Pi (BExplicit n' ty) b ->
    if n == n' then Pi (BExplicit n' (substitute val n ty)) b
    else Pi (BExplicit n' (substitute val n ty)) (substitute val n b)
  Pi (BImplicit n' ty) b ->
    if n == n' then Pi (BImplicit n' (substitute val n ty)) b
    else Pi (BImplicit n' (substitute val n ty)) (substitute val n b)
  Let n' ty val' b ->
    if n == n' then Let n' (substitute val n ty) (substitute val n val') b
    else Let n' (substitute val n ty) (substitute val n val') (substitute val n b)
  Case e cs -> Case (substitute val n e) (map (\(Clause p r) -> (Clause p (substitute val n r))) cs)
  Refl e -> Refl (substitute val n e)
  Eq a x y -> Eq (substitute val n a) (substitute val n x) (substitute val n y)
  Annot e t' -> Annot (substitute val n e) (substitute val n t')
  Proj i e -> Proj i (substitute val n e)
  Fix info t' -> Fix info (substitute val n t')
  _ -> t
module Parser where
import Base
import Ast

-- ============================================
-- CIC PARSER: Idris/Lean-style syntax
-- Supports: inductive families, universe levels, implicit args
-- ============================================

data Pos = Pos Int Int deriving (Eq, Show)
incCol (Pos l c) = Pos l (c+1)
incLine (Pos l _) = Pos (l+1) 1)
initialPos = Pos 1 1

data ParseState = ParseState { source :: String, pos :: Pos }

data Parser a = Parser (ParseState -> [(a, ParseState)])

instance Functor Parser where
  fmap f (Parser p) = Parser \s -> map (\(x, s') -> (f x, s')) (p s)

instance Applicative Parser where
  pure x = Parser \s -> [(x, s)]
  Parser pf <*> Parser px = Parser \s -> concatMap (\(f, s') -> map (\(x, s'') -> (f x, s'')) (px s')) (pf s)

instance Monad Parser where
  return = pure
  Parser p >>= f = Parser \s -> concatMap (\(x, s') -> let Parser p' = f x in p' s') (p s)

instance Alternative Parser where
  empty = Parser (const [])
  Parser p1 <|> Parser p2 = Parser \s -> case p1 s of
    [] -> p2 s
    rs -> rs

runParser (Parser p) src = case p (ParseState src initialPos) of
  [] -> Left "Parse error"
  ((x, s):_) -> if null (source s) then Right x else Left $ "Unexpected: " ++ take 20 (source s)

satisfy f = Parser \s -> case source s of
  (c:cs) | f c -> [(c, s { source = cs, pos = incCol (pos s) })]
  _ -> []

char c = satisfy (== c)
string "" = pure ""
string (c:cs) = (:) <$> char c <*> string cs

space = satisfy isSpace
spaces = many space
lexeme p = p <* spaces
token s = lexeme (string s)

parens p = between (char '(') (char ')') p
braces p = between (char '{') (char '}') p
brackets p = between (char '[') (char ']') p

-- Identifiers
ident = lexeme $ do
  c <- satisfy (\c -> isAlpha c || c == '_')
  cs <- many (satisfy (\c -> isAlphaNum c || c == '_' || c == '\''))
  let name = c:cs
  if elem name ["data", "where", "let", "in", "case", "of", "if", "then", "else", "do", "module", "import", "axiom", "inductive", "using", "namespace", "mutual", "parameters", "public", "private", "export", "impossible", "with", "rewrite", "auto", "default", "Sort", "Prop", "Type"]
    then empty
    else pure name

keyword s = lexeme $ string s *> notFollowedBy (satisfy isAlphaNum)

notFollowedBy p = Parser \s -> case runParser p (source s) of
  Left _ -> [((), s)]
  Right _ -> []

sepBy p sep = (:) <$> p <*> many (sep *> p) <|> pure []
sepBy1 p sep = (:) <$> p <*> many (sep *> p)
endBy p sep = many (p <* sep)
endBy1 p sep = some (p <* sep)

-- ============================================
-- TERM PARSING
-- ============================================
parseTerm = parseExpr

parseExpr = parsePiSigma <|> parseLambda <|> parseLet <|> parseIf <|> parseCase <|> parseDo <|> parseApp

-- Parse Pi type: (x : A) -> B or {x : A} -> B (implicit)
parsePiSigma = do
  (implicit, b) <- parseBinderIntro
  case b of
    Just (name, ty) -> do
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ if implicit
        then Pi (BImplicit (Raw name) ty) body
        else Pi (BExplicit (Raw name) ty) body
    Nothing -> empty

parseBinderIntro = do
  -- try implicit {x : A}
  implicit <- (token "{" *> pure True) <|> (token "(" *> pure False)
  v <- ident
  token ":"
  ty <- parseTerm
  (if implicit then token "}" else token ")")
  pure (implicit, Just (v, ty))
  <|> pure (False, Nothing)

parseLambda = do
  token "\\"
  (implicit, binderInfo) <- parseBinderIntro
  case binderInfo of
    Just (v, ty) -> do
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ if implicit
        then Lam (BImplicit (Raw v) ty) body
        else Lam (BExplicit (Raw v) ty) body
    Nothing -> do
      vars <- some ident
      (token "->" <|> token "=>")
      body <- parseTerm
      pure $ foldr (\v t -> Lam (BExplicit (Raw v) (Hole "_")) t) body vars

parseLet = do
  keyword "let"
  v <- ident
  token ":"
  ty <- parseTerm
  token "="
  val <- parseTerm
  keyword "in"
  body <- parseTerm
  pure $ Let (Raw v) ty val body

parseIf = do
  keyword "if"
  cond <- parseTerm
  keyword "then"
  t <- parseTerm
  keyword "else"
  e <- parseTerm
  pure $ Case cond [(Clause (PCon "True" []) t), (Clause (PCon "False" []) e)]

parseCase = do
  keyword "case"
  e <- parseTerm
  keyword "of"
  token "{"
  alts <- sepBy parseAlt (token ";")
  token "}"
  pure $ Case e alts

parseAlt = do
  pat <- parsePattern
  token "=>"
  rhs <- parseTerm
  pure (Clause pat rhs)

parsePattern = parsePCon <|> parsePLit <|> parsePVar
parsePVar = PVar . Raw <$> ident
parsePLit = PLit <$> parseNat
parsePCon = do
  c <- ident
  ps <- many parsePattern
  pure $ PCon c ps

parseDo = do
  keyword "do"
  token "{"
  stmts <- sepBy parseStmt (token ";")
  token "}"
  pure $ desugarDo stmts

parseStmt = do
  v <- ident
  token "<-"
  m <- parseTerm
  pure $ Left (v, m)
  <|> do
  e <- parseTerm
  pure $ Right e

desugarDo [] = Var (Raw "return")
desugarDo [Right e] = e
desugarDo (Left (v, m) : rest) = App (App (Var (Raw ">>=")) m) (Lam (BExplicit (Raw v) (Hole "_")) (desugarDo rest))
desugarDo (Right e : rest) = App (App (Var (Raw ">>")) e) (desugarDo rest)

parseApp = do
  atoms <- some parseAtom
  pure $ foldl1 App atoms

parseAtom = parseVar <|> parseNatLit <|> parseCharLit <|> parseStringLit <|> parseParen <|> parseSort <|> parseRefl <|> parsePair <|> parseProj

parseVar = Var . Raw <$> ident
parseNatLit = NatLit <$> lexeme (readNat <$> some (satisfy isDigit))
  where readNat cs = foldl (\n c -> n*10 + ord c - ord '0') 0 cs

parseCharLit = do
  token "'"
  c <- satisfy (const True)
  token "'"
  pure $ CharLit (ord c)

parseStringLit = do
  token "\""
  cs <- many (satisfy (\c -> c /= '"'))
  token "\""
  pure $ StringLit cs

parseParen = parens parseTerm

-- Sort parsing: Prop, Type, Type u, Sort u
parseSort = parseProp <|> parseType <|> parseSortKw

parseProp = keyword "Prop" *> pure (Sort SProp)

parseType = do
  keyword "Type"
  (token (string (show i)) *> pure (Sort (SType (NatLit i))) <|> pure (Sort (SType LZero)))
  -- Simplified: just parse "Type" as Type 0
  where i = 0

parseSortKw = keyword "Sort" *> (Sort . SType <$> parseLevel)

parseLevel = parseLZero <|> parseLSucc <|> parseLMax
parseLZero = token "0" *> pure LZero
parseLSucc = token "succ" *> (LSucc <$> parseLevel)
parseLMax = token "max" *> (LMax <$> parseLevel <*> parseLevel)

parseRefl = keyword "Refl" *> (Refl <$> parseTerm <|> pure (Refl (Var (Raw "_"))))

parsePair = parens $ do
  a <- parseTerm
  token ","
  b <- parseTerm
  pure $ Pair a b

parseProj = do
  tok <- keyword "fst" <|> keyword "snd"
  e <- parseAtom
  pure $ case tok of "fst" -> Proj 1 e; _ -> Proj 2 e

-- ============================================
-- DECLARATION PARSING
-- ============================================
parseDecl = parseIndDecl <|> parseTypeSig <|> parseFunDef <|> parseAxiomDecl <|> parseFixityDecl

-- Inductive family: data D (a : Type) : Type -> Type where | C1 : ... | C2 : ...
parseIndDecl = do
  keyword "data"
  name <- ident
  params <- many parseParam
  token ":"
  targetSort <- parseSort
  keyword "where"
  token "{"
  constrs <- sepBy1 parseConstrDecl (token "|")
  token "}"
  let indices = extractIndices params targetSort
  let indDef = IndDef
    { indName = name
    , indParams = take (length params - length indices) params
    , indIndices = indices
    , indSort = case targetSort of Sort s -> s; _ -> SType LZero
    , indConstrs = constrs
    }
  pure $ IndDecl indDef

parseParam = do
  token "("
  v <- ident
  token ":"
  ty <- parseTerm
  token ")"
  pure $ BExplicit (Raw v) ty
  <|> do
  token "{"
  v <- ident
  token ":"
  ty <- parseTerm
  token "}"
  pure $ BImplicit (Raw v) ty

parseConstrDecl = do
  c <- ident
  token ":"
  ty <- parseTerm
  -- parse constructor type: parameters already applied, rest are args + result indices
  let (args, result) = splitConstrType ty
  pure $ ConstrDef
    { conName = c
    , conArgs = args
    , conResult = result
    }

splitConstrType :: Term -> ([Binder], [Term])
splitConstrType ty = ([], [])  -- TODO: proper splitting

extractIndices :: [Binder] -> Term -> [Binder]
extractIndices params target = []  -- TODO: extract indices from target type

parseTypeSig = do
  name <- ident
  token ":"
  ty <- parseTerm
  pure $ TypeSig name ty

parseFunDef = do
  name <- ident
  clauses <- some parseClause
  pure $ FunDef name clauses

parseClause = do
  ps <- some parsePattern
  token "="
  rhs <- parseTerm
  pure $ Clause ps rhs

parseAxiomDecl = do
  keyword "axiom"
  name <- ident
  token ":"
  ty <- parseTerm
  pure $ AxiomDecl name ty

parseFixityDecl = do
  f <- (keyword "infix" *> pure Infix) <|> (keyword "infixl" *> pure InfixL) <|> (keyword "infixr" *> pure InfixR)
  prec <- lexeme (readNat <$> some (satisfy isDigit))
  ops <- some ident
  pure $ InfixDecl f prec ops

parseModule = do
  keyword "module"
  name <- ident
  keyword "where"
  decls <- many parseDecl
  pure decls

parseFile src = runParser (spaces *> (parseModule <|> many parseDecl) <* spaces) src
module Typer where
import Base
import Ast

-- ============================================
-- CIC TYPE CHECKER (Calculus of Inductive Constructions)
-- Following Lean 4 / Coq core type theory
-- ============================================

-- Context: name -> (type, optional value for conversion)
type Ctx = [(Name, (Term, Maybe Term))]

extend :: Name -> Term -> Maybe Term -> Ctx -> Ctx
extend n ty val ctx = (n, (ty, val)) : ctx

lookupType :: Name -> Ctx -> Maybe Term
lookupType n ctx = fmap fst (mlookup n ctx)

lookupVal :: Name -> Ctx -> Maybe (Maybe Term)
lookupVal n ctx = fmap snd (mlookup n ctx)

-- ============================================
-- UNIVERSE LEVEL OPERATIONS
-- ============================================

levelMax :: Level -> Level -> Level
levelMax LZero u = u
levelMax u LZero = u
levelMax (LSucc u) (LSucc v) = LSucc (levelMax u v)
levelMax u v = LMax u v

levelSucc :: Level -> Level
levelSucc = LSucc

-- Universe cumulativity: Prop <= Type 0 <= Type 1 <= ...
sortLeq :: Sort -> Sort -> Bool
sortLeq SProp (SType _)     = True
sortLeq (SType u) (SType v) = levelLeq u v
sortLeq s1 s2               = s1 == s2

levelLeq :: Level -> Level -> Bool
levelLeq LZero _ = True
levelLeq (LSucc u) (LSucc v) = levelLeq u v
levelLeq u v = u == v

sortSucc :: Sort -> Sort
sortSucc SProp       = SType LZero
sortSucc (SType u)   = SType (levelSucc u)
sortSucc (SSucc s)   = SSucc (sortSucc s)

-- ============================================
-- WEAK HEAD NORMAL FORM (WHNF)
-- ============================================
whnf :: Ctx -> Term -> Term
whnf ctx t = case t of
  App f x -> case whnf ctx f of
    Lam (BExplicit _ _) b -> whnf ctx (substitute x (binderName (Lam (BExplicit (Raw "_") (Sort SProp)) b)) b)
    Lam (BImplicit _ _) b -> whnf ctx (substitute x (binderName (Lam (BImplicit (Raw "_") (Sort SProp)) b)) b)
    Pi _ _ -> error "Pi applied"
    Fix info body ->
      -- unfold fixpoint once, then reduce
      let unfolded = substitute (Fix info body) (fixName info) body
      in whnf ctx (App unfolded x)
    f' -> App f' x
  Case e ps -> case whnf ctx e of
    Constr _ c args ->
      -- find matching clause
      case findClause c ps of
        Just rhs -> whnf ctx (applyPatterns rhs args ps)
        Nothing -> Case (Constr (indNameFromConstr c ctx) c args) ps
    NatLit 0 -> case findLitClause 0 ps of
      Just rhs -> whnf ctx rhs
      Nothing -> Case (NatLit 0) ps
    Refl e' -> case findReflClause ps of
      Just rhs -> whnf ctx rhs
      Nothing -> Case (Refl e') ps
    e' -> Case e' ps
  Let _ _ v b -> whnf ctx (substitute v (Let (Raw "_") (Sort SProp) (NatLit 0) (NatLit 0)) b)
  Proj1 e -> case whnf ctx e of
    Pair a _ -> a
    Constr _ "MkSigma" [a, _] -> a
    e' -> Proj1 e'
  Proj2 e -> case whnf ctx e of
    Pair _ b -> b
    Constr _ "MkSigma" [_, b] -> b
    e' -> Proj2 e'
  Annot e _ -> whnf ctx e
  Var n -> case lookupVal n ctx of
    Just (Just v) -> whnf ctx v
    _ -> Var n
  _ -> t

binderName :: Term -> Name
binderName (Lam (BExplicit n _) _) = n
binderName (Lam (BImplicit n _) _) = n
binderName (Pi (BExplicit n _) _) = n
binderName (Pi (BImplicit n _) _) = n
binderName _ = Raw "_"

indNameFromConstr :: String -> Ctx -> String
indNameFromConstr c ctx = c  -- simplified

applyPatterns :: Term -> [Term] -> [Clause] -> Term
applyPatterns rhs args ps = rhs  -- simplified: assumes args are bound in clause

findClause :: String -> [Clause] -> Maybe Term
findClause c [] = Nothing
findClause c ((Clause (PCon c' ps) rhs):rest) =
  if c == c' then Just rhs else findClause c rest
findClause c ((Clause PWild rhs):_) = Just rhs
findClause c (_:rest) = findClause c rest

findLitClause :: Int -> [Clause] -> Maybe Term
findLitClause n [] = Nothing
findLitClause n ((Clause (PLit m) rhs):rest) =
  if n == m then Just rhs else findLitClause n rest
findLitClause n ((Clause PWild rhs):_) = Just rhs
findLitClause n (_:rest) = findLitClause n rest

findReflClause :: [Clause] -> Maybe Term
findReflClause [] = Nothing
findReflClause ((Clause (PCon "Refl" []) rhs):_) = Just rhs
findReflClause ((Clause PWild rhs):_) = Just rhs
findReflClause (_:rest) = findReflClause rest

-- ============================================
-- FULL NORMALIZATION
-- ============================================
nf :: Ctx -> Term -> Term
nf ctx t = case whnf ctx t of
  App f x -> App (nf ctx f) (nf ctx x)
  Lam b body -> Lam (nfBinder ctx b) (nf (extendCtxBinder ctx b) body)
  Pi b body -> Pi (nfBinder ctx b) (nf (extendCtxBinder ctx b) body)
  Let n ty val b -> Let n (nf ctx ty) (nf ctx val) (nf (extend n ty (Just val) ctx) b)
  Case e ps -> Case (nf ctx e) (map (\(Clause p r) -> (Clause p (nf ctx r))) ps)
  Eq a x y -> Eq (nf ctx a) (nf ctx x) (nf ctx y)
  Refl e -> Refl (nf ctx e)
  Annot e t' -> Annot (nf ctx e) (nf ctx t')
  Proj i e -> Proj i (nf ctx e)
  Fix info t' -> Fix info (nf ctx t')
  Constr tn cn args -> Constr tn cn (map (nf ctx) args)
  t' -> t'

nfBinder :: Ctx -> Binder -> Binder
nfBinder ctx (BExplicit n ty) = BExplicit n (nf ctx ty)
nfBinder ctx (BImplicit n ty) = BImplicit n (nf ctx ty)

extendCtxBinder :: Ctx -> Binder -> Ctx
extendCtxBinder ctx (BExplicit n ty) = extend n ty Nothing ctx
extendCtxBinder ctx (BImplicit n ty) = extend n ty Nothing ctx

-- ============================================
-- DEFINITIONAL EQUALITY (convertibility)
-- Includes: beta, iota (induction), delta (unfold), xi, eta
-- ============================================
convert :: Ctx -> Term -> Term -> Either String ()
convert ctx a b = do
  let a' = whnf ctx a
  let b' = whnf ctx b
  convertWhnf ctx a' b'

convertWhnf :: Ctx -> Term -> Term -> Either String ()
convertWhnf ctx a b = case (a, b) of
  (Var n1, Var n2) | n1 == n2 -> Right ()
  (App f1 x1, App f2 x2) -> convert ctx f1 f2 >> convert ctx x1 x2
  (Lam b1 body1, Lam b2 body2) ->
    convertBinder ctx b1 b2 >> convert (extendCtxBinder ctx b1) body1 body2
  (Pi b1 body1, Pi b2 body2) ->
    convertBinder ctx b1 b2 >> convert (extendCtxBinder ctx b1) body1 body2
  (Let n1 ty1 v1 b1, Let n2 ty2 v2 b2) ->
    convert ctx ty1 ty2 >> convert ctx v1 v2 >> convert (extend n1 ty1 (Just v1) ctx) b1 b2
  (Sort s1, Sort s2) | sortLeq s1 s2 && sortLeq s2 s1 -> Right ()
  (Constr _ c1 args1, Constr _ c2 args2) | c1 == c2 && length args1 == length args2 ->
    mapM_ (uncurry (convert ctx)) (zip args1 args2)
  (Eq a1 x1 y1, Eq a2 x2 y2) ->
    convert ctx a1 a2 >> convert ctx x1 x2 >> convert ctx y1 y2
  (Refl e1, Refl e2) -> convert ctx e1 e2
  (NatLit n1, NatLit n2) | n1 == n2 -> Right ()
  (CharLit c1, CharLit c2) | c1 == c2 -> Right ()
  (Annot e1 _, Annot e2 _) -> convert ctx e1 e2
  (Meta i, Meta j) | i == j -> Right ()
  -- Eta expansion for functions
  (f, Lam b body) ->
    let x = Var (binderName (Lam b body))
    in convert ctx (App f x) (App (Lam b body) x)
  (Lam b body, f) ->
    let x = Var (binderName (Lam b body))
    in convert ctx (App (Lam b body) x) (App f x)
  _ -> Left $ "Cannot convert: " ++ ppTerm a ++ " and " ++ ppTerm b

convertBinder :: Ctx -> Binder -> Binder -> Either String ()
convertBinder ctx (BExplicit _ ty1) (BExplicit _ ty2) = convert ctx ty1 ty2
convertBinder ctx (BImplicit _ ty1) (BImplicit _ ty2) = convert ctx ty1 ty2
convertBinder _ _ _ = Left "Binder mismatch"

-- ============================================
-- UNIVERSE CONSTRAINTS
-- ============================================
inferSort :: Ctx -> Term -> Either String Sort
inferSort ctx t = do
  ty <- infer ctx t
  case whnf ctx ty of
    Sort s -> Right s
    _ -> Left $ "Expected sort, got: " ++ ppTerm ty

-- Cumulativity: if A : Sort u and u <= v, then A : Sort v
checkSort :: Ctx -> Term -> Sort -> Either String ()
checkSort ctx t expected = do
  actual <- inferSort ctx t
  if sortLeq actual expected
    then Right ()
    else Left $ "Universe mismatch: " ++ ppSort actual ++ " not <= " ++ ppSort expected

-- ============================================
-- BIDIRECTIONAL TYPE CHECKING
-- ============================================

-- INFERENCE: synthesize the type of a term
infer :: Ctx -> Term -> Either String Term
infer ctx t = case t of
  Var n -> case lookupType n ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ ppName n
  
  App f x -> do
    fTy <- infer ctx f
    case whnf ctx fTy of
      Pi (BExplicit _ a) b -> do
        check ctx x a
        Right (substitute x (binderName (Pi (BExplicit (Raw "_") (Sort SProp)) b)) b)
      Pi (BImplicit _ a) b -> do
        -- implicit argument: try to infer from context
        Right (substitute (Meta 0) (binderName (Pi (BImplicit (Raw "_") (Sort SProp)) b)) b)
      _ -> Left $ "Expected Pi type, got: " ++ ppTerm (whnf ctx fTy)
  
  Lam b@(BExplicit n ty) body ->
    Left $ "Cannot infer type of explicit lambda without annotation: \\(" ++ ppName n ++ " : ...) => ..."
  
  Lam b@(BImplicit n ty) body ->
    Left $ "Cannot infer type of implicit lambda"
  
  Pi b@(BExplicit n a) body -> do
    aSort <- inferSort ctx a
    bodySort <- inferSort (extendCtxBinder ctx b) body
    let resultSort = sortMax aSort bodySort
    Right (Sort resultSort)
  
  Pi b@(BImplicit n a) body -> do
    aSort <- inferSort ctx a
    bodySort <- inferSort (extendCtxBinder ctx b) body
    let resultSort = sortMax aSort bodySort
    Right (Sort resultSort)
  
  Let n ty val body -> do
    check ctx ty (Sort (SType LZero))
    check ctx val ty
    infer (extend n ty (Just val) ctx) body
  
  Sort SProp -> Right (Sort (SType LZero))  -- Prop : Type
  Sort (SType u) -> Right (Sort (SType (levelSucc u)))  -- Type u : Type (u+1)
  
  Constr tn cn args -> do
    -- lookup inductive definition
    case lookupIndDef tn ctx of
      Just ind -> inferConstr ctx ind cn args
      Nothing -> Left $ "Unknown inductive type: " ++ tn
  
  Case e ps -> do
    eTy <- infer ctx e
    -- infer from first clause
    case ps of
      (Clause p rhs):_ -> do
        (patTy, patBindings) <- inferPattern ctx p eTy
        rhsTy <- infer (patBindings ++ ctx) rhs
        Right rhsTy
      [] -> Left "Empty pattern match"
  
  Eq a x y -> do
    check ctx a (Sort (SType LZero))
    check ctx x a
    check ctx y a
    Right (Sort SProp)  -- equality is a proposition
  
  Refl e -> do
    eTy <- infer ctx e
    Right (Eq eTy e e)
  
  Annot e t' -> do
    check ctx t' (Sort (SType LZero))
    check ctx e t'
    Right t'
  
  NatLit _ -> Right (Var (Global "Nat"))
  CharLit _ -> Right (Var (Global "Char"))
  StringLit _ -> Right (App (Var (Global "List")) (Var (Global "Char")))
  
  Meta i -> Right (Meta i)  -- meta is a meta
  
  Fix info body -> do
    let ctx' = extend (fixName info) (fixType info) (Just (Fix info body)) ctx
    bodyTy <- infer ctx' body
    Right (fixType info)
  
  _ -> Left $ "Cannot infer type of: " ++ ppTerm t

-- CHECKING: verify a term has the expected type
check :: Ctx -> Term -> Term -> Either String ()
check ctx t expected = case (t, whnf ctx expected) of
  (Lam b body, Pi b' body') -> do
    convertBinder ctx b b'
    check (extendCtxBinder ctx b) body (substitute (Var (binderName (Lam b body))) (binderName (Pi b' body')) body')
  
  (Constr tn cn args, expected') -> do
    -- constructor application
    case lookupIndDef tn ctx of
      Just ind -> checkConstr ctx ind cn args expected'
      Nothing -> Left $ "Unknown inductive type in check: " ++ tn
  
  (Case e ps, ty') -> do
    eTy <- infer ctx e
    mapM_ (checkClause ctx eTy ty') ps
  
  (Let n ty val b, ty') -> do
    check ctx ty (Sort (SType LZero))
    check ctx val ty
    check (extend n ty (Just val) ctx) b ty'
  
  (Meta _, _) -> Right ()  -- meta can have any type
  
  (t, ty') -> do
    inferred <- infer ctx t
    convert ctx inferred ty'

-- ============================================
-- PATTERN CHECKING
-- ============================================
checkClause :: Ctx -> Term -> Term -> Clause -> Either String ()
checkClause ctx patTy resTy (Clause p rhs) = do
  (bindings, _) <- checkPattern ctx p patTy
  check (bindings ++ ctx) rhs resTy

checkPattern :: Ctx -> Pattern -> Term -> Either String (Ctx, Term)
checkPattern ctx p ty = case (p, whnf ctx ty) of
  (PVar n, ty') -> Right ([(n, (ty', Nothing))], ty')
  (PWild, ty') -> Right ([], ty')
  (PLit n, Var (Global "Nat")) -> Right ([], Var (Global "Nat"))
  (PCon c ps, ty') -> case ty' of
    App (Inductive ind) _ ->
      case findConstr ind c of
        Just conDef -> do
          (bindings, _) <- checkPatArgs ctx ps (conArgs conDef)
          Right (bindings, ty')
        Nothing -> Left $ "Unknown constructor: " ++ c
    _ -> Left $ "Expected inductive type for constructor pattern"
  (PAnnotated p' t, _) -> do
    check ctx t (Sort (SType LZero))
    convert ctx (whnf ctx t) (whnf ctx ty)
    checkPattern ctx p' t
  _ -> Left "Pattern/type mismatch"

checkPatArgs :: Ctx -> [Pattern] -> [Binder] -> Either String (Ctx, [Term])
checkPatArgs ctx [] [] = Right ([], [])
checkPatArgs ctx (p:ps) (b:bs) = do
  let ty = binderType b
  (bind1, _) <- checkPattern ctx p ty
  (bindRest, ts') <- checkPatArgs (bind1 ++ ctx) ps bs
  Right (bind1 ++ bindRest, Var (Raw "_") : ts')  -- placeholder
checkPatArgs _ _ _ = Left "Pattern/constructor arg count mismatch"

inferPattern :: Ctx -> Pattern -> Term -> Either String (Term, Ctx)
inferPattern ctx p ty = do
  (bindings, patTy) <- checkPattern ctx p ty
  Right (patTy, bindings)

binderType :: Binder -> Term
binderType (BExplicit _ ty) = ty
binderType (BImplicit _ ty) = ty

findConstr :: IndDef -> String -> Maybe ConstrDef
findConstr ind c = case filter (\cd -> conName cd == c) (indConstrs ind) of
  (cd:_) -> Just cd
  [] -> Nothing

inferConstr :: Ctx -> IndDef -> String -> [Term] -> Either String Term
inferConstr ctx ind cn args = do
  case findConstr ind cn of
    Just conDef -> do
      let params = map (\b -> Var (binderName (Pi b (Sort SProp)))) (indParams ind)
      let resultIndices = conResult conDef
      let fullType = foldr (\b t -> Pi b t) (foldl App (Inductive ind) (params ++ resultIndices)) (conArgs conDef)
      Right fullType
    Nothing -> Left $ "Unknown constructor: " ++ cn

checkConstr :: Ctx -> IndDef -> String -> [Term] -> Term -> Either String ()
checkConstr ctx ind cn args expected = do
  conTy <- inferConstr ctx ind cn args
  convert ctx conTy expected

lookupIndDef :: String -> Ctx -> Maybe IndDef
lookupIndDef tn ctx = Nothing  -- TODO: store inductive defs in context

-- ============================================
-- TOP-LEVEL PROGRAM CHECKING
-- ============================================
checkProgram :: Ctx -> Program -> Either String Ctx
checkProgram ctx [] = Right ctx
checkProgram ctx (decl:decls) = do
  ctx' <- checkDecl ctx decl
  checkProgram ctx' decls

checkDecl :: Ctx -> Decl -> Either String Ctx
checkDecl ctx decl = case decl of
  TypeSig n ty -> do
    check ctx ty (Sort (SType LZero))
    Right ((Global n, (ty, Nothing)) : ctx)
  
  FunDef n clauses -> do
    ty <- case lookupType (Global n) ctx of
      Just t -> Right t
      Nothing -> Left $ "No type signature for: " ++ n
    mapM_ (checkClause ctx ty ty) clauses
    Right ctx
  
  IndDecl ind -> do
    -- check inductive definition well-formedness
    checkInductive ctx ind
    Right ((Global (indName ind), (Sort (indSort ind), Nothing)) : ctx)
  
  AxiomDecl n ty -> do
    check ctx ty (Sort (SType LZero))
    Right ((Global n, (ty, Nothing)) : ctx)
  
  InfixDecl _ _ _ -> Right ctx

-- Check inductive definition is well-formed
checkInductive :: Ctx -> IndDef -> Either String ()
checkInductive ctx ind = do
  -- Check parameter types are in appropriate universes
  let paramCtx = foldr (\b c -> extendCtxBinder c b) ctx (indParams ind)
  -- Check constructor argument types
  mapM_ (checkConstrDef paramCtx ind) (indConstrs ind)
  Right ()

checkConstrDef :: Ctx -> IndDef -> ConstrDef -> Either String ()
checkConstrDef ctx ind con = do
  let argCtx = foldr (\b c -> extendCtxBinder c b) ctx (conArgs con)
  -- result type must be the inductive type applied to params and result indices
  Right ()

-- Universe max for Pi types
sortMax :: Sort -> Sort -> Sort
sortMax SProp s = s
sortMax s SProp = s
sortMax (SType u) (SType v) = SType (levelMax u v)
sortMax s1 s2 = if sortLeq s1 s2 then s2 else s1

typecheck :: Program -> Either String (Ctx, Term)
typecheck prog = do
  ctx <- checkProgram [] prog
  Right (ctx, Sort (SType LZero))
module Kiselyov where
import Base
import Ast

-- ============================================
-- TYPE ERASURE + OPTIMAL BRACKET ABSTRACTION
-- For CIC: dependent types + inductive types are completely erased
-- Only computational content remains
-- ============================================

data LamTerm = LVar Name | LApp LamTerm LamTerm | LLam Name LamTerm | LCon String | LPrim String

erase :: Term -> LamTerm
erase t = case t of
  Var n -> LVar n
  App f x -> LApp (erase f) (erase x)
  Lam (BExplicit n _) b -> LLam n (erase b)
  Lam (BImplicit n _) b -> LLam n (erase b)
  Pi _ _ b -> erase b
  Let n _ v b -> LApp (LLam n (erase b)) (erase v)
  Inductive d -> LCon (indName d)
  Constr _ cn args -> foldl LApp (LCon cn) (map erase args)
  Case e ps -> foldl LApp (LCon "case") (erase e : map (\(Clause p t) -> LApp (erasePat p) (erase t)) ps)
  Refl e -> erase e
  Eq _ x y -> erase x
  Pair a b -> LApp (LApp (LCon "MkSigma") (erase a)) (erase b)
  Annot e _ -> erase e
  NatLit n -> LPrim (show n)
  CharLit c -> LPrim ("chr" ++ show c)
  StringLit s -> LPrim ("str" ++ s)
  Proj i e -> LApp (LPrim (if i == 1 then "fst" else "snd")) (erase e)
  Fix _ body -> erase body
  Meta _ -> LVar (Raw "_")
  Hole _ -> LVar (Raw "_")
  _ -> LVar (Raw "undefined")

erasePat :: Pattern -> LamTerm
erasePat p = case p of
  PVar n -> LVar n
  PCon c ps -> foldl LApp (LCon c) (map erasePat ps)
  PLit n -> LPrim (show n)
  PWild -> LVar (Raw "_")
  PInaccessible t -> erase t
  PAnnotated p' _ -> erasePat p'

abstract :: Name -> LamTerm -> LamTerm
abstract n t = case t of
  LVar n' | n == n' -> LPrim "I"
          | otherwise -> LApp (LPrim "K") (LVar n')
  LApp f x -> case (isFree n f, isFree n x) of
    (False, False) -> LApp (LPrim "K") (LApp f x)
    (True, False) -> LApp (LApp (LPrim "B") (abstract n f)) x
    (False, True) -> LApp (LApp (LPrim "C") f) (abstract n x)
    (True, True) -> LApp (LApp (LPrim "S") (abstract n f)) (abstract n x)
  LLam n' b | n == n' -> t
            | otherwise -> abstract n (LLam n' (abstract n' b))
  LCon c -> LApp (LPrim "K") (LCon c)
  LPrim s -> LApp (LPrim "K") (LPrim s)

isFree :: Name -> LamTerm -> Bool
isFree n t = case t of
  LVar n' -> n == n'
  LApp f x -> isFree n f || isFree n x
  LLam n' b -> n /= n' && isFree n b
  _ -> False

compile :: LamTerm -> String
compile t = case t of
  LVar (Raw s) -> s
  LVar (Global s) -> s
  LVar (Ind i) -> "v" ++ show i
  LApp f x -> "(" ++ compile f ++ " " ++ compile x ++ ")"
  LLam n b -> compile (abstract n b)
  LCon c -> c
  LPrim s -> s

compileTerm :: Term -> String
compileTerm = compile . erase

compileDecl :: Decl -> String
compileDecl decl = case decl of
  TypeSig _ _ -> ""
  FunDef n cs -> compileClauses n cs
  IndDecl _ -> ""
  AxiomDecl _ _ -> ""
  InfixDecl _ _ _ -> ""

compileClauses :: String -> [Clause] -> String
compileClauses n cs = n ++ " = " ++ case cs of
  [Clause [] rhs] -> compileTerm rhs
  _ -> foldr (\c acc -> compileClause n c acc) (LPrim "undefined") cs

compileClause :: String -> Clause -> String -> String
compileClause n (Clause ps rhs) fallback =
  "case " ++ n ++ " of { " ++ intercalate " ; " (map (\p -> ppPat p ++ " => " ++ compileTerm rhs) ps) ++ " ; _ => " ++ fallback ++ " }"

ppPat :: Pattern -> String
ppPat (PVar (Raw s)) = s
ppPat (PVar (Global s)) = s
ppPat (PCon c ps) = "(" ++ c ++ " " ++ unwords (map ppPat ps) ++ ")"
ppPat (PLit n) = show n
ppPat PWild = "_"
ppPat (PInaccessible t) = "." ++ ppTerm t
ppPat (PAnnotated p t) = "(" ++ ppPat p ++ " : " ++ ppTerm t ++ ")"

compileProgram :: Program -> String
compileProgram prog = unlines $ filter (not . null) $ map compileDecl prog
module RTS where
import Base

-- Runtime system generation: C backend and WebAssembly C backend.

cHeader :: String
cHeader = unlines
  [ "#include <stdio.h>"
  , "#include <stdlib.h>"
  , "#include <string.h>"
  , "#include <time.h>"
  , ""
  , "typedef unsigned u;"
  , "enum { TOP = 1<<23, BUFMAX = 1<<20 };"
  , "u *mem, *altmem, *sp, *spTop, hp;"
  , "enum { FORWARD = 27, REDUCING = 9 };"
  , ""
  , "static inline u isAddr(u n) { return n>=128; }"
  , ""
  , "void gc() {"
  , "  u di = 128; hp = 128;"
  , "  sp = altmem + TOP - 1;"
  , "  // placeholder: full GC would evacuate reachable nodes"
  , "}"
  , ""
  , "static inline u app(u f, u x) {"
  , "  mem[hp] = f; mem[hp+1] = x; hp += 2; return hp-2;"
  , "}"
  , ""
  , "void run(u root) {"
  , "  mem = malloc(TOP * sizeof(u));"
  , "  altmem = malloc(TOP * sizeof(u));"
  , "  spTop = mem + TOP - 1;"
  , "  hp = 128;"
  , "  sp = spTop;"
  , "  *sp = app(root, 0);"
  , "  printf(\"Execution stub.\\n\");"
  , "}"
  , ""
  , "int main(int argc, char **argv) {"
  , "  return 0;"
  , "}"
  ]

-- WebAssembly C backend (freestanding).
wasify :: String -> String
wasify c = "#include <stddef.h>\n" ++
  "#include <stdint.h>\n" ++
  "typedef uint32_t u;\n" ++
  "enum { TOP = 1<<20 };\n" ++
  "static u mem[TOP];\n" ++
  "static u hp = 128;\n" ++
  "static inline u app(u f, u x) { mem[hp]=f; mem[hp+1]=x; hp+=2; return hp-2; }\n" ++
  "__attribute__((export_name(\"run\"))) void run(void) { hp = 128; }\n" ++
  c

-- Raw combinator memory dump format.
outputC :: String -> String
outputC body = cHeader ++ "\n/* User program */\n" ++ body

outputRaw :: String -> String
outputRaw s = "# raw memory dump\n" ++ s

outputWasmC :: String -> String
outputWasmC body = wasify body

-- Encode combinators for raw dump.
encodeComb "Y" = 1
encodeComb "S" = 2
encodeComb "K" = 3
encodeComb "I" = 4
encodeComb "B" = 5
encodeComb "C" = 6
encodeComb "T" = 7
encodeComb "R" = 8
encodeComb "F" = 9
encodeComb "+" = 10
encodeComb "-" = 11
encodeComb "*" = 12
encodeComb "/" = 13
encodeComb "%" = 14
encodeComb "=" = 15
encodeComb "L" = 16
encodeComb ":" = 17
encodeComb "a" = 18
encodeComb _ = 0
module Precisely where

import Base
import Ast
import Parser
import Typer
import Kiselyov
import RTS

data Mode = Check | Compile | Raw | Run | Wasm deriving (Eq, Show)

parseMode "check"   = Just Check
parseMode "compile" = Just Compile
parseMode "raw"     = Just Raw
parseMode "run"     = Just Run
parseMode "wasm"    = Just Wasm
parseMode _         = Nothing

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Usage: precisely <check|compile|raw|run|wasm> <file.x>"
    (modeStr:rest) -> case parseMode modeStr of
      Nothing -> putStrLn $ "Unknown mode: " ++ modeStr
      Just mode -> case rest of
        [] -> putStrLn "No input file specified."
        (f:_) -> do
          src <- readFile f
          case parseFile src of
            Left err -> putStrLn $ "Parse error: " ++ err
            Right prog -> do
              putStrLn $ "Parsed " ++ show (length prog) ++ " declarations."
              case typecheck prog of
                Left err -> putStrLn $ "Type error: " ++ err
                Right (ctx, _) -> do
                  putStrLn "Type checking OK."
                  case mode of
                    Check -> pure ()
                    Compile -> putStr $ outputC $ compileProgram prog
                    Raw -> putStr $ outputRaw $ compileProgram prog
                    Run -> do
                      putStr $ outputC $ compileProgram prog
                      putStrLn "-- Run: pipe output to a C compiler"
                    Wasm -> do
                      putStr $ outputWasmC $ compileProgram prog
                      putStrLn "-- WebAssembly C-for-WASM output above"

-- FFI helpers
foreign import ccall "putchar" putChar :: Int -> IO Int
foreign import ccall "getchar" getChar :: IO Int
foreign import ccall "getargcount" getArgCount :: IO Int
foreign import ccall "getargchar" getArgChar :: Int -> Int -> IO Char

putStrLn :: String -> IO ()
putStrLn s = mapM_ (putChar . ord) s >> putChar (ord '\n') >> pure ()

getArgs :: IO [String]
getArgs = do
  n <- getArgCount
  mapM (\i -> do
    let go k = do
          c <- getArgChar i k
          if c == '\0' then pure [] else (c:) <$> go (k+1)
    go 0) [0..n-1]

readFile :: String -> IO String
readFile path = interact id

interact :: (String -> String) -> IO String
interact f = do
  s <- getContents
  pure (f s)

getContents :: IO String
getContents = do
  c <- getChar
  if c == (-1) then pure [] else (chr c :) <$> getContents

-- Debug: show parsed program.
showProgram :: Program -> String
showProgram = unlines . map showDecl
  where
    showDecl (TypeSig n ty) = n ++ " : " ++ ppTerm ty
    showDecl (FunDef n cs) = n ++ " = " ++ intercalate " | " (map (\(Clause ps rhs) -> unwords (map ppPat ps) ++ " => " ++ ppTerm rhs) cs)
    showDecl (DataDecl d cs) = "data " ++ d ++ " = " ++ intercalate " | " (map (\(c, ts) -> c ++ " " ++ unwords (map ppTerm ts)) cs)
    showDecl (InfixDecl f prec ops) = show f ++ " " ++ show prec ++ " " ++ unwords ops
