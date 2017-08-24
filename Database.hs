{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Database where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r x h y =
  eq_rect x h y

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type _ _ c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' ->
    case m of {
     O -> n;
     S m' -> S (max n' m')}}

min :: Nat -> Nat -> Nat
min n m =
  case n of {
   O -> O;
   S n' ->
    case m of {
     O -> O;
     S m' -> S (min n' m')}}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

n_rect :: a1 -> (Positive -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Positive -> a1) -> N -> a1
n_rec =
  n_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: (a1 -> a1) -> a1 -> Positive -> a1
iter f x n =
  case n of {
   XI n' -> f (iter f (iter f x n') n');
   XO n' -> iter f (iter f x n') n';
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x =
  iter (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add0 (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ (size p0);
   XO p0 -> succ (size p0);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

eqb :: Positive -> Positive -> Bool
eqb p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb p0 q0;
     _ -> False};
   XO p0 ->
    case q of {
     XO q0 -> eqb p0 q0;
     _ -> False};
   XH ->
    case q of {
     XH -> True;
     _ -> False}}

leb :: Positive -> Positive -> Bool
leb x y =
  case compare x y of {
   Gt -> False;
   _ -> True}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> (Prod
                Positive Mask) -> Prod Positive Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair (XI s) (sub_mask r' s');
       False -> Pair (XO s) (IsPos r')};
     _ -> Pair (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> Prod Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> Pair XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> Pair XH (IsPos XH)};
   XH -> Pair XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI _ -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (add (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> Prod Positive
         (Prod Positive Positive)
ggcdn n a b =
  case n of {
   O -> Pair XH (Pair a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa (add0 aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add0 bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa (XO bb))}};
       XH -> Pair XH (Pair a XH)};
     XO a0 ->
      case b of {
       XI _ ->
        case ggcdn n0 a0 b of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair (XO g) p};
       XH -> Pair XH (Pair a XH)};
     XH -> Pair XH (Pair XH b)}}

ggcd :: Positive -> Positive -> Prod Positive (Prod Positive Positive)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH ->
    case q of {
     XO q0 -> XI q0;
     _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH ->
    case q of {
     XO _ -> N0;
     _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH ->
    case q of {
     XO _ -> Npos XH;
     _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH ->
    case q of {
     XI q0 -> Npos (XO q0);
     XO q0 -> Npos (XI q0);
     XH -> N0}}

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter (\x -> XO x) p n0}

testbit_nat :: Positive -> Nat -> Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> True;
     S _ -> False}}

testbit :: Positive -> N -> Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> True;
     Npos _ -> False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\_ h y0 ->
    case y0 of {
     XI p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0);
     _ -> Right}) (\_ h y0 ->
    case y0 of {
     XO p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0);
     _ -> Right}) (\y0 ->
    case y0 of {
     XH -> Left;
     _ -> Right}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ (XO p0)) (f (XO p0) x))} in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

zero :: N
zero =
  N0

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos _ -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

min0 :: N -> N -> N
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: N -> N -> N
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add0 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add0 x' y')}}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos _ -> Lt;
     Zneg _ -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

leb0 :: Z -> Z -> Bool
leb0 x y =
  case compare1 x y of {
   Gt -> False;
   _ -> True}

ltb :: Z -> Z -> Bool
ltb x y =
  case compare1 x y of {
   Lt -> True;
   _ -> False}

max1 :: Z -> Z -> Z
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

type T = Z

_0 :: Z
_0 =
  Z0

_1 :: Z
_1 =
  Zpos XH

_2 :: Z
_2 =
  Zpos (XO XH)

add2 :: Z -> Z -> Z
add2 =
  add1

max2 :: Z -> Z -> Z
max2 =
  max1

ltb0 :: Z -> Z -> Bool
ltb0 =
  ltb

leb1 :: Z -> Z -> Bool
leb1 =
  leb0

gt_le_dec :: Z -> Z -> Sumbool
gt_le_dec i j =
  let {b = ltb j i} in
  case b of {
   True -> Left;
   False -> Right}

ge_lt_dec :: Z -> Z -> Sumbool
ge_lt_dec i j =
  let {b = ltb i j} in
  case b of {
   True -> Right;
   False -> Left}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of {
   Nil -> a0;
   Cons b t -> f b (fold_right f a0 t)}

data Compare x =
   LT
 | EQ
 | GT

compare_rect :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) ->
                (Compare a1) -> a2
compare_rect _ _ f f0 f1 c =
  case c of {
   LT -> f __;
   EQ -> f0 __;
   GT -> f1 __}

compare_rec :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) -> (Compare
               a1) -> a2
compare_rec x y =
  compare_rect x y

type T0 = N

zero0 :: N
zero0 =
  N0

one :: N
one =
  Npos XH

two :: N
two =
  Npos (XO XH)

succ_double0 :: N -> N
succ_double0 x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double0 :: N -> N
double0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ1 :: N -> N
succ1 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

pred :: N -> N
pred n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
   Npos p -> succ p}

add3 :: N -> N -> N
add3 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (add0 p q)}}

sub0 :: N -> N -> N
sub0 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare2 :: N -> N -> Comparison
compare2 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos _ -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

eqb0 :: N -> N -> Bool
eqb0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> True;
     Npos _ -> False};
   Npos p ->
    case m of {
     N0 -> False;
     Npos q -> eqb p q}}

leb2 :: N -> N -> Bool
leb2 x y =
  case compare2 x y of {
   Gt -> False;
   _ -> True}

ltb1 :: N -> N -> Bool
ltb1 x y =
  case compare2 x y of {
   Lt -> True;
   _ -> False}

min1 :: N -> N -> N
min1 n n' =
  case compare2 n n' of {
   Gt -> n';
   _ -> n}

max3 :: N -> N -> N
max3 n n' =
  case compare2 n n' of {
   Gt -> n;
   _ -> n'}

div2 :: N -> N
div2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Bool
even n =
  case n of {
   N0 -> True;
   Npos p ->
    case p of {
     XO _ -> True;
     _ -> False}}

odd :: N -> Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos XH;
   Npos p0 ->
    case n of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos (size p);
     XO p -> Npos (size p);
     XH -> N0}}

size0 :: N -> N
size0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Nat
size_nat0 n =
  case n of {
   N0 -> O;
   Npos p -> size_nat p}

pos_div_eucl :: Positive -> N -> Prod N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double0 r} in
      case leb2 b r' of {
       True -> Pair (succ_double0 q) (sub0 r' b);
       False -> Pair (double0 q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double0 r} in
      case leb2 b r' of {
       True -> Pair (succ_double0 q) (sub0 r' b);
       False -> Pair (double0 q) r'}};
   XH ->
    case b of {
     N0 -> Pair N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> Pair (Npos XH) N0;
       _ -> Pair N0 (Npos XH)}}}

div_eucl :: N -> N -> Prod N N
div_eucl a b =
  case a of {
   N0 -> Pair N0 N0;
   Npos na ->
    case b of {
     N0 -> Pair N0 a;
     Npos _ -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> Prod N (Prod N N)
ggcd0 a b =
  case a of {
   N0 -> Pair b (Pair N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> Pair a (Pair (Npos XH) N0);
     Npos q ->
      case ggcd p q of {
       Pair g p0 ->
        case p0 of {
         Pair aa bb -> Pair (Npos g) (Pair (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> Prod N N
sqrtrem0 n =
  case n of {
   N0 -> Pair N0 N0;
   Npos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Npos s) (Npos r);
       _ -> Pair (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> lxor p q}}

shiftl_nat :: N -> Nat -> N
shiftl_nat a =
  nat_rect a (\_ -> double0)

shiftr_nat :: N -> Nat -> N
shiftr_nat a =
  nat_rect a (\_ -> div2)

shiftl0 :: N -> N -> N
shiftl0 a n =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n)}

shiftr :: N -> N -> N
shiftr a n =
  case n of {
   N0 -> a;
   Npos p -> iter div2 a p}

testbit_nat0 :: N -> Nat -> Bool
testbit_nat0 a =
  case a of {
   N0 -> (\_ -> False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Bool
testbit0 a n =
  case a of {
   N0 -> False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat :: Nat -> N
of_nat n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  case n of {
   N0 -> x;
   Npos p -> iter f x p}

eq_dec0 :: N -> N -> Sumbool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Left;
     Npos _ -> Right}) (\p m0 ->
    case m0 of {
     N0 -> Right;
     Npos p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p0)}) n m

discr :: N -> Sumor Positive
discr n =
  case n of {
   N0 -> Inright;
   Npos p -> Inleft p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec =
  peano_rect0

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

leb_spec0 :: N -> N -> Reflect
leb_spec0 x y =
  iff_reflect (leb2 x y)

ltb_spec0 :: N -> N -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb1 x y)

max_case_strong :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                   -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: N -> N -> Sumbool
max_dec n m =
  max_case n m (\_ _ _ h0 -> h0) Left Right

min_case_strong :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                   -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: N -> N -> Sumbool
min_dec n m =
  min_case n m (\_ _ _ h0 -> h0) Left Right

max_case_strong0 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

max_case0 :: N -> N -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: N -> N -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

min_case0 :: N -> N -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: N -> N -> Sumbool
min_dec0 =
  min_dec

sqrt_up :: N -> N
sqrt_up a =
  case compare2 N0 a of {
   Lt -> succ1 (sqrt0 (pred a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare2 (Npos XH) a of {
   Lt -> succ1 (log2 (pred a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec :: N -> N -> Reflect
eqb_spec x y =
  iff_reflect (eqb0 x y)

b2n :: Bool -> N
b2n b =
  case b of {
   True -> Npos XH;
   False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos XH) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos XH) n)

ones :: N -> N
ones n =
  pred (shiftl0 (Npos XH) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

data String =
   EmptyString
 | String0 Ascii0 String

type T1 = N

eq_dec1 :: N -> N -> Sumbool
eq_dec1 =
  eq_dec0

compare3 :: N -> N -> Compare N
compare3 x y =
  let {
   c = compSpec2Type x y
         (case x of {
           N0 ->
            case y of {
             N0 -> Eq;
             Npos _ -> Lt};
           Npos n' ->
            case y of {
             N0 -> Gt;
             Npos m' -> compare n' m'}})}
  in
  case c of {
   CompEqT -> EQ;
   CompLtT -> LT;
   CompGtT -> GT}

type T2 = N

eq_dec2 :: N -> N -> Sumbool
eq_dec2 =
  eq_dec0

compare4 :: N -> N -> Compare N
compare4 x y =
  let {
   c = compSpec2Type x y
         (case x of {
           N0 ->
            case y of {
             N0 -> Eq;
             Npos _ -> Lt};
           Npos n' ->
            case y of {
             N0 -> Gt;
             Npos m' -> compare n' m'}})}
  in
  case c of {
   CompEqT -> EQ;
   CompLtT -> LT;
   CompGtT -> GT}

type Key = N

data Tree elt =
   Leaf
 | Node (Tree elt) Key elt (Tree elt) T

tree_rect :: a2 -> ((Tree a1) -> a2 -> Key -> a1 -> (Tree a1) -> a2 -> T ->
             a2) -> (Tree a1) -> a2
tree_rect f f0 t =
  case t of {
   Leaf -> f;
   Node t0 k e t1 t2 ->
    f0 t0 (tree_rect f f0 t0) k e t1 (tree_rect f f0 t1) t2}

tree_rec :: a2 -> ((Tree a1) -> a2 -> Key -> a1 -> (Tree a1) -> a2 -> T ->
            a2) -> (Tree a1) -> a2
tree_rec =
  tree_rect

height :: (Tree a1) -> T
height m =
  case m of {
   Leaf -> _0;
   Node _ _ _ _ h -> h}

cardinal :: (Tree a1) -> Nat
cardinal m =
  case m of {
   Leaf -> O;
   Node l _ _ r _ -> S (add (cardinal l) (cardinal r))}

empty :: Tree a1
empty =
  Leaf

is_empty :: (Tree a1) -> Bool
is_empty m =
  case m of {
   Leaf -> True;
   Node _ _ _ _ _ -> False}

mem :: N -> (Tree a1) -> Bool
mem x m =
  case m of {
   Leaf -> False;
   Node l y _ r _ ->
    case compare3 x y of {
     LT -> mem x l;
     EQ -> True;
     GT -> mem x r}}

find :: N -> (Tree a1) -> Option a1
find x m =
  case m of {
   Leaf -> None;
   Node l y d r _ ->
    case compare3 x y of {
     LT -> find x l;
     EQ -> Some d;
     GT -> find x r}}

create :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
create l x e r =
  Node l x e r (add2 (max2 (height l) (height r)) _1)

assert_false :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
assert_false =
  create

bal :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
bal l x d r =
  let {hl = height l} in
  let {hr = height r} in
  case gt_le_dec hl (add2 hr _2) of {
   Left ->
    case l of {
     Leaf -> assert_false l x d r;
     Node ll lx ld lr _ ->
      case ge_lt_dec (height ll) (height lr) of {
       Left -> create ll lx ld (create lr x d r);
       Right ->
        case lr of {
         Leaf -> assert_false l x d r;
         Node lrl lrx lrd lrr _ ->
          create (create ll lx ld lrl) lrx lrd (create lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add2 hl _2) of {
     Left ->
      case r of {
       Leaf -> assert_false l x d r;
       Node rl rx rd rr _ ->
        case ge_lt_dec (height rr) (height rl) of {
         Left -> create (create l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf -> assert_false l x d r;
           Node rll rlx rld rlr _ ->
            create (create l x d rll) rlx rld (create rlr rx rd rr)}}};
     Right -> create l x d r}}

add4 :: Key -> a1 -> (Tree a1) -> Tree a1
add4 x d m =
  case m of {
   Leaf -> Node Leaf x d Leaf _1;
   Node l y d' r h ->
    case compare3 x y of {
     LT -> bal (add4 x d l) y d' r;
     EQ -> Node l y d r h;
     GT -> bal l y d' (add4 x d r)}}

remove_min :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Prod (Tree a1)
              (Prod Key a1)
remove_min l x d r =
  case l of {
   Leaf -> Pair r (Pair x d);
   Node ll lx ld lr _ ->
    case remove_min ll lx ld lr of {
     Pair l' m -> Pair (bal l' x d r) m}}

merge :: (Tree a1) -> (Tree a1) -> Tree a1
merge s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node l2 x2 d2 r2 _ ->
      case remove_min l2 x2 d2 r2 of {
       Pair s2' p ->
        case p of {
         Pair x d -> bal s1 x d s2'}}}}

remove :: N -> (Tree a1) -> Tree a1
remove x m =
  case m of {
   Leaf -> Leaf;
   Node l y d r _ ->
    case compare3 x y of {
     LT -> bal (remove x l) y d r;
     EQ -> merge l r;
     GT -> bal l y d (remove x r)}}

join :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
join l =
  case l of {
   Leaf -> add4;
   Node ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf -> add4 x d l;
        Node rl rx rd rr rh ->
         case gt_le_dec lh (add2 rh _2) of {
          Left -> bal ll lx ld (join lr x d r);
          Right ->
           case gt_le_dec rh (add2 lh _2) of {
            Left -> bal (join_aux rl) rx rd rr;
            Right -> create l x d r}}}}
    in join_aux)}

data Triple elt =
   Mktriple (Tree elt) (Option elt) (Tree elt)

t_left :: (Triple a1) -> Tree a1
t_left t =
  case t of {
   Mktriple t_left1 _ _ -> t_left1}

t_opt :: (Triple a1) -> Option a1
t_opt t =
  case t of {
   Mktriple _ t_opt0 _ -> t_opt0}

t_right :: (Triple a1) -> Tree a1
t_right t =
  case t of {
   Mktriple _ _ t_right1 -> t_right1}

split :: N -> (Tree a1) -> Triple a1
split x m =
  case m of {
   Leaf -> Mktriple Leaf None Leaf;
   Node l y d r _ ->
    case compare3 x y of {
     LT ->
      case split x l of {
       Mktriple ll o rl -> Mktriple ll o (join rl y d r)};
     EQ -> Mktriple l (Some d) r;
     GT ->
      case split x r of {
       Mktriple rl o rr -> Mktriple (join l y d rl) o rr}}}

concat :: (Tree a1) -> (Tree a1) -> Tree a1
concat m1 m2 =
  case m1 of {
   Leaf -> m2;
   Node _ _ _ _ _ ->
    case m2 of {
     Leaf -> m1;
     Node l2 x2 d2 r2 _ ->
      case remove_min l2 x2 d2 r2 of {
       Pair m2' xd -> join m1 (fst xd) (snd xd) m2'}}}

elements_aux :: (List (Prod Key a1)) -> (Tree a1) -> List (Prod Key a1)
elements_aux acc m =
  case m of {
   Leaf -> acc;
   Node l x d r _ -> elements_aux (Cons (Pair x d) (elements_aux acc r)) l}

elements :: (Tree a1) -> List (Prod Key a1)
elements =
  elements_aux Nil

fold :: (Key -> a1 -> a2 -> a2) -> (Tree a1) -> a2 -> a2
fold f m a =
  case m of {
   Leaf -> a;
   Node l x d r _ -> fold f r (f x d (fold f l a))}

data Enumeration elt =
   End
 | More Key elt (Tree elt) (Enumeration elt)

enumeration_rect :: a2 -> (Key -> a1 -> (Tree a1) -> (Enumeration a1) -> a2
                    -> a2) -> (Enumeration a1) -> a2
enumeration_rect f f0 e =
  case e of {
   End -> f;
   More k e0 t e1 -> f0 k e0 t e1 (enumeration_rect f f0 e1)}

enumeration_rec :: a2 -> (Key -> a1 -> (Tree a1) -> (Enumeration a1) -> a2 ->
                   a2) -> (Enumeration a1) -> a2
enumeration_rec =
  enumeration_rect

cons :: (Tree a1) -> (Enumeration a1) -> Enumeration a1
cons m e =
  case m of {
   Leaf -> e;
   Node l x d r _ -> cons l (More x d r e)}

equal_more :: (a1 -> a1 -> Bool) -> N -> a1 -> ((Enumeration a1) -> Bool) ->
              (Enumeration a1) -> Bool
equal_more cmp x1 d1 cont e2 =
  case e2 of {
   End -> False;
   More x2 d2 r2 e3 ->
    case compare3 x1 x2 of {
     EQ ->
      case cmp d1 d2 of {
       True -> cont (cons r2 e3);
       False -> False};
     _ -> False}}

equal_cont :: (a1 -> a1 -> Bool) -> (Tree a1) -> ((Enumeration a1) -> Bool)
              -> (Enumeration a1) -> Bool
equal_cont cmp m1 cont e2 =
  case m1 of {
   Leaf -> cont e2;
   Node l1 x1 d1 r1 _ ->
    equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2}

equal_end :: (Enumeration a1) -> Bool
equal_end e2 =
  case e2 of {
   End -> True;
   More _ _ _ _ -> False}

equal :: (a1 -> a1 -> Bool) -> (Tree a1) -> (Tree a1) -> Bool
equal cmp m1 m2 =
  equal_cont cmp m1 equal_end (cons m2 End)

map0 :: (a1 -> a2) -> (Tree a1) -> Tree a2
map0 f m =
  case m of {
   Leaf -> Leaf;
   Node l x d r h -> Node (map0 f l) x (f d) (map0 f r) h}

mapi :: (Key -> a1 -> a2) -> (Tree a1) -> Tree a2
mapi f m =
  case m of {
   Leaf -> Leaf;
   Node l x d r h -> Node (mapi f l) x (f x d) (mapi f r) h}

map_option :: (Key -> a1 -> Option a2) -> (Tree a1) -> Tree a2
map_option f m =
  case m of {
   Leaf -> Leaf;
   Node l x d r _ ->
    case f x d of {
     Some d' -> join (map_option f l) x d' (map_option f r);
     None -> concat (map_option f l) (map_option f r)}}

map2_opt :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree a1) -> Tree 
            a3) -> ((Tree a2) -> Tree a3) -> (Tree a1) -> (Tree a2) -> Tree
            a3
map2_opt f mapl mapr m1 m2 =
  case m1 of {
   Leaf -> mapr m2;
   Node l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf -> mapl m1;
     Node _ _ _ _ _ ->
      case split x1 m2 of {
       Mktriple l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join (map2_opt f mapl mapr l1 l2') x1 e
            (map2_opt f mapl mapr r1 r2');
         None ->
          concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')}}}}

map2 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree a1) -> (Tree 
        a2) -> Tree a3
map2 f =
  map2_opt (\_ d o -> f (Some d) o) (map_option (\_ d -> f (Some d) None))
    (map_option (\_ d' -> f None (Some d')))

type T3 = N

eq_dec3 :: N -> N -> Sumbool
eq_dec3 =
  eq_dec1

lt_dec :: N -> N -> Sumbool
lt_dec x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare3 x y)

eqb1 :: N -> N -> Bool
eqb1 x y =
  case eq_dec3 x y of {
   Left -> True;
   Right -> False}

type T4 = N

eq_dec4 :: N -> N -> Sumbool
eq_dec4 =
  eq_dec1

lt_dec0 :: N -> N -> Sumbool
lt_dec0 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare3 x y)

eqb2 :: N -> N -> Bool
eqb2 x y =
  case eq_dec4 x y of {
   Left -> True;
   Right -> False}

type T5 = N

eq_dec5 :: N -> N -> Sumbool
eq_dec5 =
  eq_dec1

lt_dec1 :: N -> N -> Sumbool
lt_dec1 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare3 x y)

eqb3 :: N -> N -> Bool
eqb3 x y =
  case eq_dec5 x y of {
   Left -> True;
   Right -> False}

type T6 = N

eq_dec6 :: N -> N -> Sumbool
eq_dec6 =
  eq_dec1

lt_dec2 :: N -> N -> Sumbool
lt_dec2 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare3 x y)

eqb4 :: N -> N -> Bool
eqb4 x y =
  case eq_dec6 x y of {
   Left -> True;
   Right -> False}

type Key0 = N

type T7 elt = List (Prod N elt)

empty0 :: T7 a1
empty0 =
  Nil

is_empty0 :: (T7 a1) -> Bool
is_empty0 l =
  case l of {
   Nil -> True;
   Cons _ _ -> False}

mem0 :: Key0 -> (T7 a1) -> Bool
mem0 k s =
  case s of {
   Nil -> False;
   Cons p l ->
    case p of {
     Pair k' _ ->
      case compare3 k k' of {
       LT -> False;
       EQ -> True;
       GT -> mem0 k l}}}

data R_mem elt =
   R_mem_0 (T7 elt)
 | R_mem_1 (T7 elt) N elt (List (Prod N elt))
 | R_mem_2 (T7 elt) N elt (List (Prod N elt))
 | R_mem_3 (T7 elt) N elt (List (Prod N elt)) Bool (R_mem elt)

r_mem_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
              (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
              (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
              a1 -> (List (Prod N a1)) -> () -> () -> () -> Bool -> (R_mem
              a1) -> a2 -> a2) -> (T7 a1) -> Bool -> (R_mem a1) -> a2
r_mem_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_0 s -> f s __;
   R_mem_1 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_2 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_3 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect k f f0 f1 f2 l _res r0)}

r_mem_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
             (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
             (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
             a1 -> (List (Prod N a1)) -> () -> () -> () -> Bool -> (R_mem 
             a1) -> a2 -> a2) -> (T7 a1) -> Bool -> (R_mem a1) -> a2
r_mem_rec k =
  r_mem_rect k

mem_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
            (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
            (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
            a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7
            a1) -> a2
mem_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> False;
      Cons p l ->
       case p of {
        Pair k' _ ->
         case compare3 k k' of {
          LT -> False;
          EQ -> True;
          GT -> mem0 k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ -> let {hrec = mem_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare3 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (mem0 k s)

mem_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
           (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
           (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1
           -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7 
           a1) -> a2
mem_rec k =
  mem_rect k

r_mem_correct :: Key0 -> (T7 a1) -> Bool -> R_mem a1
r_mem_correct k s _res =
  let {princ = \x -> mem_rect x} in
  unsafeCoerce princ k (\y _ z _ -> eq_rect_r False (R_mem_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r False (R_mem_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r True (R_mem_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (mem0 k y2) (R_mem_3 y y0 y1 y2 (mem0 k y2)
      (y6 (mem0 k y2) __)) z) s _res __

find0 :: Key0 -> (T7 a1) -> Option a1
find0 k s =
  case s of {
   Nil -> None;
   Cons p s' ->
    case p of {
     Pair k' x ->
      case compare3 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find0 k s'}}}

data R_find elt =
   R_find_0 (T7 elt)
 | R_find_1 (T7 elt) N elt (List (Prod N elt))
 | R_find_2 (T7 elt) N elt (List (Prod N elt))
 | R_find_3 (T7 elt) N elt (List (Prod N elt)) (Option elt) (R_find elt)

r_find_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
               (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1
               -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
               a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () ->
               (Option a1) -> (R_find a1) -> a2 -> a2) -> (T7 a1) -> (Option
               a1) -> (R_find a1) -> a2
r_find_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_find_0 s -> f s __;
   R_find_1 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_2 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_3 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect k f f0 f1 f2 s' _res r0)}

r_find_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
              (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
              (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
              a1 -> (List (Prod N a1)) -> () -> () -> () -> (Option a1) ->
              (R_find a1) -> a2 -> a2) -> (T7 a1) -> (Option a1) -> (R_find
              a1) -> a2
r_find_rec k =
  r_find_rect k

find_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
             (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
             (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
             a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7
             a1) -> a2
find_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> None;
      Cons p s' ->
       case p of {
        Pair k' x ->
         case compare3 k k' of {
          LT -> None;
          EQ -> Some x;
          GT -> find0 k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare3 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (find0 k s)

find_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
            (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
            (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
            a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7
            a1) -> a2
find_rec k =
  find_rect k

r_find_correct :: Key0 -> (T7 a1) -> (Option a1) -> R_find a1
r_find_correct k s _res =
  let {princ = \x -> find_rect x} in
  unsafeCoerce princ k (\y _ z _ -> eq_rect_r None (R_find_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r None (R_find_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r (Some y1) (R_find_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (find0 k y2) (R_find_3 y y0 y1 y2 (find0 k y2)
      (y6 (find0 k y2) __)) z) s _res __

add5 :: Key0 -> a1 -> (T7 a1) -> T7 a1
add5 k x s =
  case s of {
   Nil -> Cons (Pair k x) Nil;
   Cons p l ->
    case p of {
     Pair k' y ->
      case compare3 k k' of {
       LT -> Cons (Pair k x) s;
       EQ -> Cons (Pair k x) l;
       GT -> Cons (Pair k' y) (add5 k x l)}}}

data R_add elt =
   R_add_0 (T7 elt)
 | R_add_1 (T7 elt) N elt (List (Prod N elt))
 | R_add_2 (T7 elt) N elt (List (Prod N elt))
 | R_add_3 (T7 elt) N elt (List (Prod N elt)) (T7 elt) (R_add elt)

r_add_rect :: Key0 -> a1 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 ->
              (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
              a1 -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
              a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> (T7
              a1) -> (R_add a1) -> a2 -> a2) -> (T7 a1) -> (T7 a1) -> (R_add
              a1) -> a2
r_add_rect k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_0 s -> f s __;
   R_add_1 s k' y l -> f0 s k' y l __ __ __;
   R_add_2 s k' y l -> f1 s k' y l __ __ __;
   R_add_3 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect k x f f0 f1 f2 l _res r0)}

r_add_rec :: Key0 -> a1 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 ->
             (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
             a1 -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
             a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> (T7
             a1) -> (R_add a1) -> a2 -> a2) -> (T7 a1) -> (T7 a1) -> (R_add
             a1) -> a2
r_add_rec k x =
  r_add_rect k x

add_rect :: Key0 -> a1 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 ->
            (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
            a1 -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
            a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 ->
            a2) -> (T7 a1) -> a2
add_rect k x f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Cons (Pair k x) Nil;
      Cons p l ->
       case p of {
        Pair k' y ->
         case compare3 k k' of {
          LT -> Cons (Pair k x) s;
          EQ -> Cons (Pair k x) l;
          GT -> Cons (Pair k' y) (add5 k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare3 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (add5 k x s)

add_rec :: Key0 -> a1 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 ->
           (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1
           -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
           a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7 
           a1) -> a2
add_rec k x =
  add_rect k x

r_add_correct :: Key0 -> a1 -> (T7 a1) -> (T7 a1) -> R_add a1
r_add_correct k x s _res =
  add_rect k x (\y _ z _ -> eq_rect_r (Cons (Pair k x) Nil) (R_add_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y) (R_add_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y2) (R_add_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (add5 k x y2)) (R_add_3 y y0 y1 y2
      (add5 k x y2) (y6 (add5 k x y2) __)) z) s _res __

remove0 :: Key0 -> (T7 a1) -> T7 a1
remove0 k s =
  case s of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k' x ->
      case compare3 k k' of {
       LT -> s;
       EQ -> l;
       GT -> Cons (Pair k' x) (remove0 k l)}}}

data R_remove elt =
   R_remove_0 (T7 elt)
 | R_remove_1 (T7 elt) N elt (List (Prod N elt))
 | R_remove_2 (T7 elt) N elt (List (Prod N elt))
 | R_remove_3 (T7 elt) N elt (List (Prod N elt)) (T7 elt) (R_remove elt)

r_remove_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 ->
                 (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
                 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () ->
                 a2) -> ((T7 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> ()
                 -> () -> (T7 a1) -> (R_remove a1) -> a2 -> a2) -> (T7 
                 a1) -> (T7 a1) -> (R_remove a1) -> a2
r_remove_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_0 s -> f s __;
   R_remove_1 s k' x l -> f0 s k' x l __ __ __;
   R_remove_2 s k' x l -> f1 s k' x l __ __ __;
   R_remove_3 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect k f f0 f1 f2 l _res r0)}

r_remove_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
                (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1
                -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
                a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> (T7
                a1) -> (R_remove a1) -> a2 -> a2) -> (T7 a1) -> (T7 a1) ->
                (R_remove a1) -> a2
r_remove_rec k =
  r_remove_rect k

remove_rect :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
               (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1
               -> (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 
               a1) -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> a2
               -> a2) -> (T7 a1) -> a2
remove_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Nil;
      Cons p l ->
       case p of {
        Pair k' x ->
         case compare3 k k' of {
          LT -> s;
          EQ -> l;
          GT -> Cons (Pair k' x) (remove0 k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare3 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (remove0 k s)

remove_rec :: Key0 -> ((T7 a1) -> () -> a2) -> ((T7 a1) -> N -> a1 -> (List
              (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N -> a1 ->
              (List (Prod N a1)) -> () -> () -> () -> a2) -> ((T7 a1) -> N ->
              a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) -> (T7
              a1) -> a2
remove_rec k =
  remove_rect k

r_remove_correct :: Key0 -> (T7 a1) -> (T7 a1) -> R_remove a1
r_remove_correct k s _res =
  let {princ = \x -> remove_rect x} in
  unsafeCoerce princ k (\y _ z _ -> eq_rect_r Nil (R_remove_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y (R_remove_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y2 (R_remove_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (remove0 k y2)) (R_remove_3 y y0 y1 y2
      (remove0 k y2) (y6 (remove0 k y2) __)) z) s _res __

elements0 :: (T7 a1) -> T7 a1
elements0 m =
  m

fold0 :: (Key0 -> a1 -> a2 -> a2) -> (T7 a1) -> a2 -> a2
fold0 f m acc =
  case m of {
   Nil -> acc;
   Cons p m' ->
    case p of {
     Pair k e -> fold0 f m' (f k e acc)}}

data R_fold elt a =
   R_fold_0 (Key0 -> elt -> a -> a) (T7 elt) a
 | R_fold_1 (Key0 -> elt -> a -> a) (T7 elt) a N elt (List (Prod N elt)) 
 a (R_fold elt a)

r_fold_rect :: (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> () ->
               a2) -> (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any ->
               N -> a1 -> (List (Prod N a1)) -> () -> Any -> (R_fold 
               a1 Any) -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> (T7 
               a1) -> a3 -> a3 -> (R_fold a1 a3) -> a2
r_fold_rect f f0 _ _ _ _ r =
  case r of {
   R_fold_0 f1 m acc -> unsafeCoerce f __ f1 m acc __;
   R_fold_1 f1 m acc k e m' _res r0 ->
    unsafeCoerce f0 __ f1 m acc k e m' __ _res r0
      (r_fold_rect f f0 f1 m' (f1 k e acc) _res r0)}

r_fold_rec :: (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> () ->
              a2) -> (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> N
              -> a1 -> (List (Prod N a1)) -> () -> Any -> (R_fold a1 
              Any) -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> (T7 a1) -> a3
              -> a3 -> (R_fold a1 a3) -> a2
r_fold_rec f f0 f1 m acc a r =
  r_fold_rect f f0 f1 m acc a r

fold_rect :: (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> () -> a2)
             -> (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> N ->
             a1 -> (List (Prod N a1)) -> () -> a2 -> a2) -> (Key0 -> a1 -> a3
             -> a3) -> (T7 a1) -> a3 -> a2
fold_rect f0 f f1 m acc =
  eq_rect_r
    (case m of {
      Nil -> acc;
      Cons p m' ->
       case p of {
        Pair k e -> fold0 f1 m' (f1 k e acc)}})
    (let {f2 = unsafeCoerce f0 __ f1 m acc} in
     let {f3 = unsafeCoerce f __ f1 m acc} in
     case m of {
      Nil -> f2 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect f0 f f1 l (f1 t0 e acc)} in f4 hrec}})
    (fold0 f1 m acc)

fold_rec :: (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> () -> a2)
            -> (() -> (Key0 -> a1 -> Any -> Any) -> (T7 a1) -> Any -> N -> a1
            -> (List (Prod N a1)) -> () -> a2 -> a2) -> (Key0 -> a1 -> a3 ->
            a3) -> (T7 a1) -> a3 -> a2
fold_rec f f0 f1 m acc =
  fold_rect f f0 f1 m acc

r_fold_correct :: (Key0 -> a1 -> a2 -> a2) -> (T7 a1) -> a2 -> a2 -> R_fold
                  a1 a2
r_fold_correct f m acc _res =
  let {princ = \x x0 -> fold_rect x x0} in
  unsafeCoerce princ (\_ y0 y1 y2 _ z _ ->
    eq_rect_r y2 (R_fold_0 y0 y1 y2) z) (\_ y0 y1 y2 y3 y4 y5 _ y7 z _ ->
    eq_rect_r (fold0 y0 y5 (y0 y3 y4 y2)) (R_fold_1 y0 y1 y2 y3 y4 y5
      (fold0 y0 y5 (y0 y3 y4 y2)) (y7 (fold0 y0 y5 (y0 y3 y4 y2)) __)) z) f m
    acc _res __

equal0 :: (a1 -> a1 -> Bool) -> (T7 a1) -> (T7 a1) -> Bool
equal0 cmp m m' =
  case m of {
   Nil ->
    case m' of {
     Nil -> True;
     Cons _ _ -> False};
   Cons p l ->
    case p of {
     Pair x e ->
      case m' of {
       Nil -> False;
       Cons p0 l' ->
        case p0 of {
         Pair x' e' ->
          case compare3 x x' of {
           EQ -> andb (cmp e e') (equal0 cmp l l');
           _ -> False}}}}}

data R_equal elt =
   R_equal_0 (T7 elt) (T7 elt)
 | R_equal_1 (T7 elt) (T7 elt) N elt (List (Prod N elt)) N elt (List
                                                               (Prod N elt)) 
 Bool (R_equal elt)
 | R_equal_2 (T7 elt) (T7 elt) N elt (List (Prod N elt)) N elt (List
                                                               (Prod N elt)) 
 (Compare N)
 | R_equal_3 (T7 elt) (T7 elt) (T7 elt) (T7 elt)

r_equal_rect :: (a1 -> a1 -> Bool) -> ((T7 a1) -> (T7 a1) -> () -> () -> a2)
                -> ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> ()
                -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> Bool ->
                (R_equal a1) -> a2 -> a2) -> ((T7 a1) -> (T7 a1) -> N -> a1
                -> (List (Prod N a1)) -> () -> N -> a1 -> (List (Prod N a1))
                -> () -> (Compare N) -> () -> () -> a2) -> ((T7 a1) -> (T7
                a1) -> (T7 a1) -> () -> (T7 a1) -> () -> () -> a2) -> (T7 
                a1) -> (T7 a1) -> Bool -> (R_equal a1) -> a2
r_equal_rect cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_0 m m' -> f m m' __ __;
   R_equal_1 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect cmp f f0 f1 f2 l l' _res r0);
   R_equal_2 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_3 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec :: (a1 -> a1 -> Bool) -> ((T7 a1) -> (T7 a1) -> () -> () -> a2)
               -> ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> ()
               -> N -> a1 -> (List (Prod N a1)) -> () -> () -> () -> Bool ->
               (R_equal a1) -> a2 -> a2) -> ((T7 a1) -> (T7 a1) -> N -> a1 ->
               (List (Prod N a1)) -> () -> N -> a1 -> (List (Prod N a1)) ->
               () -> (Compare N) -> () -> () -> a2) -> ((T7 a1) -> (T7 
               a1) -> (T7 a1) -> () -> (T7 a1) -> () -> () -> a2) -> (T7 
               a1) -> (T7 a1) -> Bool -> (R_equal a1) -> a2
r_equal_rec cmp =
  r_equal_rect cmp

equal_rect :: (a1 -> a1 -> Bool) -> ((T7 a1) -> (T7 a1) -> () -> () -> a2) ->
              ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> N
              -> a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) ->
              ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> N
              -> a1 -> (List (Prod N a1)) -> () -> (Compare N) -> () -> () ->
              a2) -> ((T7 a1) -> (T7 a1) -> (T7 a1) -> () -> (T7 a1) -> () ->
              () -> a2) -> (T7 a1) -> (T7 a1) -> a2
equal_rect cmp f2 f1 f0 f m m' =
  eq_rect_r
    (case m of {
      Nil ->
       case m' of {
        Nil -> True;
        Cons _ _ -> False};
      Cons p l ->
       case p of {
        Pair x e ->
         case m' of {
          Nil -> False;
          Cons p0 l' ->
           case p0 of {
            Pair x' e' ->
             case compare3 x x' of {
              EQ -> andb (cmp e e') (equal0 cmp l l');
              _ -> False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      Nil ->
       let {f9 = f3 __} in
       case m' of {
        Nil -> f9 __;
        Cons _ _ -> f8 __};
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          Nil -> f8 __;
          Cons p0 l0 ->
           case p0 of {
            Pair t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare3 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare3 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}}) (equal0 cmp m m')

equal_rec :: (a1 -> a1 -> Bool) -> ((T7 a1) -> (T7 a1) -> () -> () -> a2) ->
             ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> N
             -> a1 -> (List (Prod N a1)) -> () -> () -> () -> a2 -> a2) ->
             ((T7 a1) -> (T7 a1) -> N -> a1 -> (List (Prod N a1)) -> () -> N
             -> a1 -> (List (Prod N a1)) -> () -> (Compare N) -> () -> () ->
             a2) -> ((T7 a1) -> (T7 a1) -> (T7 a1) -> () -> (T7 a1) -> () ->
             () -> a2) -> (T7 a1) -> (T7 a1) -> a2
equal_rec cmp =
  equal_rect cmp

r_equal_correct :: (a1 -> a1 -> Bool) -> (T7 a1) -> (T7 a1) -> Bool ->
                   R_equal a1
r_equal_correct cmp m m' _res =
  equal_rect cmp (\y y0 _ _ z _ -> eq_rect_r True (R_equal_0 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    eq_rect_r (andb (cmp y2 y6) (equal0 cmp y3 y7)) (R_equal_1 y y0 y1 y2 y3
      y5 y6 y7 (equal0 cmp y3 y7) (y11 (equal0 cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    eq_rect_r False (R_equal_2 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> eq_rect_r False (R_equal_3 y y0 y1 y3) z) m m'
    _res __

map1 :: (a1 -> a2) -> (T7 a1) -> T7 a2
map1 f m =
  case m of {
   Nil -> Nil;
   Cons p m' ->
    case p of {
     Pair k e -> Cons (Pair k (f e)) (map1 f m')}}

mapi0 :: (Key0 -> a1 -> a2) -> (T7 a1) -> T7 a2
mapi0 f m =
  case m of {
   Nil -> Nil;
   Cons p m' ->
    case p of {
     Pair k e -> Cons (Pair k (f k e)) (mapi0 f m')}}

option_cons :: Key0 -> (Option a1) -> (List (Prod Key0 a1)) -> List
               (Prod Key0 a1)
option_cons k o l =
  case o of {
   Some e -> Cons (Pair k e) l;
   None -> l}

map2_l :: ((Option a1) -> (Option a2) -> Option a3) -> (T7 a1) -> T7 a3
map2_l f m =
  case m of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k e -> option_cons k (f (Some e) None) (map2_l f l)}}

map2_r :: ((Option a1) -> (Option a2) -> Option a3) -> (T7 a2) -> T7 a3
map2_r f m' =
  case m' of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair k e' -> option_cons k (f None (Some e')) (map2_r f l')}}

map3 :: ((Option a1) -> (Option a2) -> Option a3) -> (T7 a1) -> (T7 a2) -> T7
        a3
map3 f m =
  case m of {
   Nil -> map2_r f;
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       map2_aux m' =
         case m' of {
          Nil -> map2_l f m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare3 k k' of {
              LT -> option_cons k (f (Some e) None) (map3 f l m');
              EQ -> option_cons k (f (Some e) (Some e')) (map3 f l l');
              GT -> option_cons k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine :: (T7 a1) -> (T7 a2) -> T7 (Prod (Option a1) (Option a2))
combine m =
  case m of {
   Nil -> map1 (\e' -> Pair None (Some e'));
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       combine_aux m' =
         case m' of {
          Nil -> map1 (\e0 -> Pair (Some e0) None) m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare3 k k' of {
              LT -> Cons (Pair k (Pair (Some e) None)) (combine l m');
              EQ -> Cons (Pair k (Pair (Some e) (Some e'))) (combine l l');
              GT -> Cons (Pair k' (Pair None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> (List (Prod a1 a2)) -> a3 -> a3
fold_right_pair f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt :: ((Option a1) -> (Option a2) -> Option a3) -> (T7 a1) -> (T7 
            a2) -> List (Prod Key0 a3)
map2_alt f m m' =
  let {m0 = combine m m'} in
  let {m1 = map1 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair option_cons m1 Nil

at_least_one :: (Option a1) -> (Option a2) -> Option
                (Prod (Option a1) (Option a2))
at_least_one o o' =
  case o of {
   Some _ -> Some (Pair o o');
   None ->
    case o' of {
     Some _ -> Some (Pair o o');
     None -> None}}

at_least_one_then_f :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                       a1) -> (Option a2) -> Option a3
at_least_one_then_f f o o' =
  case o of {
   Some _ -> f o o';
   None ->
    case o' of {
     Some _ -> f o o';
     None -> None}}

data R_mem0 elt =
   R_mem_4 (Tree elt)
 | R_mem_5 (Tree elt) (Tree elt) Key elt (Tree elt) T Bool (R_mem0 elt)
 | R_mem_6 (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_mem_7 (Tree elt) (Tree elt) Key elt (Tree elt) T Bool (R_mem0 elt)

r_mem_rect0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key
               -> a1 -> (Tree a1) -> T -> () -> () -> () -> Bool -> (R_mem0
               a1) -> a2 -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 ->
               (Tree a1) -> T -> () -> () -> () -> a2) -> ((Tree a1) -> (Tree
               a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> Bool
               -> (R_mem0 a1) -> a2 -> a2) -> (Tree a1) -> Bool -> (R_mem0
               a1) -> a2
r_mem_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_4 m -> f m __;
   R_mem_5 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect0 x f f0 f1 f2 l _res r1);
   R_mem_6 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_7 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect0 x f f0 f1 f2 r0 _res r1)}

r_mem_rec0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key
              -> a1 -> (Tree a1) -> T -> () -> () -> () -> Bool -> (R_mem0
              a1) -> a2 -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 ->
              (Tree a1) -> T -> () -> () -> () -> a2) -> ((Tree a1) -> (Tree
              a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> Bool ->
              (R_mem0 a1) -> a2 -> a2) -> (Tree a1) -> Bool -> (R_mem0 
              a1) -> a2
r_mem_rec0 x =
  r_mem_rect0 x

data R_find0 elt =
   R_find_4 (Tree elt)
 | R_find_5 (Tree elt) (Tree elt) Key elt (Tree elt) T (Option elt) (R_find0
                                                                    elt)
 | R_find_6 (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_find_7 (Tree elt) (Tree elt) Key elt (Tree elt) T (Option elt) (R_find0
                                                                    elt)

r_find_rect0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) ->
                Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Option 
                a1) -> (R_find0 a1) -> a2 -> a2) -> ((Tree a1) -> (Tree 
                a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> a2)
                -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T ->
                () -> () -> () -> (Option a1) -> (R_find0 a1) -> a2 -> a2) ->
                (Tree a1) -> (Option a1) -> (R_find0 a1) -> a2
r_find_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_find_4 m -> f m __;
   R_find_5 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect0 x f f0 f1 f2 l _res r1);
   R_find_6 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_7 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect0 x f f0 f1 f2 r0 _res r1)}

r_find_rec0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key
               -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Option a1) ->
               (R_find0 a1) -> a2 -> a2) -> ((Tree a1) -> (Tree a1) -> Key ->
               a1 -> (Tree a1) -> T -> () -> () -> () -> a2) -> ((Tree 
               a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () ->
               () -> (Option a1) -> (R_find0 a1) -> a2 -> a2) -> (Tree 
               a1) -> (Option a1) -> (R_find0 a1) -> a2
r_find_rec0 x =
  r_find_rect0 x

data R_bal elt =
   R_bal_0 (Tree elt) Key elt (Tree elt)
 | R_bal_1 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T
 | R_bal_2 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T
 | R_bal_3 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T (Tree elt) Key elt (Tree elt) T
 | R_bal_4 (Tree elt) Key elt (Tree elt)
 | R_bal_5 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T
 | R_bal_6 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T
 | R_bal_7 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T (Tree elt) Key elt (Tree elt) T
 | R_bal_8 (Tree elt) Key elt (Tree elt)

r_bal_rect :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> a2)
              -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree
              a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> a2) ->
              ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> () ->
              a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> a2) -> ((Tree
              a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> () -> () ->
              a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> ()
              -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
              -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () ->
              () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T ->
              () -> () -> () -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree
              a1) -> () -> () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree
              a1) -> T -> () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree
              a1) -> T -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree 
              a1) -> () -> () -> () -> () -> a2) -> (Tree a1) -> Key -> a1 ->
              (Tree a1) -> (Tree a1) -> (R_bal a1) -> a2
r_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r =
  case r of {
   R_bal_0 x x0 x1 x2 -> f x x0 x1 x2 __ __ __;
   R_bal_1 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_2 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_3 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_4 x x0 x1 x2 -> f3 x x0 x1 x2 __ __ __ __ __;
   R_bal_5 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_6 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_7 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_8 x x0 x1 x2 -> f7 x x0 x1 x2 __ __ __ __}

r_bal_rec :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> a2) ->
             ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
             a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> a2) ->
             ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
             a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> () ->
             a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree
             a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Tree
             a1) -> Key -> a1 -> (Tree a1) -> T -> () -> a2) -> ((Tree 
             a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> () -> () ->
             a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () ->
             () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> ()
             -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> ()
             -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () ->
             () -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () ->
             () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> ()
             -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () ->
             a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () ->
             () -> a2) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> (Tree 
             a1) -> (R_bal a1) -> a2
r_bal_rec =
  r_bal_rect

data R_add0 elt =
   R_add_4 (Tree elt)
 | R_add_5 (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree elt) (R_add0 elt)
 | R_add_6 (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_add_7 (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree elt) (R_add0 elt)

r_add_rect0 :: Key -> a1 -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
               a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Tree
               a1) -> (R_add0 a1) -> a2 -> a2) -> ((Tree a1) -> (Tree 
               a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> a2) ->
               ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> ()
               -> () -> () -> (Tree a1) -> (R_add0 a1) -> a2 -> a2) -> (Tree
               a1) -> (Tree a1) -> (R_add0 a1) -> a2
r_add_rect0 x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_4 m -> f m __;
   R_add_5 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect0 x d f f0 f1 f2 l _res r1);
   R_add_6 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_7 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect0 x d f f0 f1 f2 r0 _res r1)}

r_add_rec0 :: Key -> a1 -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Tree
              a1) -> (R_add0 a1) -> a2 -> a2) -> ((Tree a1) -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> a2) ->
              ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () ->
              () -> () -> (Tree a1) -> (R_add0 a1) -> a2 -> a2) -> (Tree 
              a1) -> (Tree a1) -> (R_add0 a1) -> a2
r_add_rec0 x d =
  r_add_rect0 x d

data R_remove_min elt =
   R_remove_min_0 (Tree elt) Key elt (Tree elt)
 | R_remove_min_1 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T (Prod (Tree elt) (Prod Key elt)) (R_remove_min elt) (Tree elt) (Prod 
                                                                  Key 
                                                                  elt)

r_remove_min_rect :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> a2) ->
                     ((Tree a1) -> Key -> a1 -> (Tree a1) -> (Tree a1) -> Key
                     -> a1 -> (Tree a1) -> T -> () -> (Prod (Tree a1)
                     (Prod Key a1)) -> (R_remove_min a1) -> a2 -> (Tree 
                     a1) -> (Prod Key a1) -> () -> a2) -> (Tree a1) -> Key ->
                     a1 -> (Tree a1) -> (Prod (Tree a1) (Prod Key a1)) ->
                     (R_remove_min a1) -> a2
r_remove_min_rect f f0 _ _ _ _ _ r =
  case r of {
   R_remove_min_0 l x d r0 -> f l x d r0 __;
   R_remove_min_1 l x d r0 ll lx ld lr _x _res r1 l' m ->
    f0 l x d r0 ll lx ld lr _x __ _res r1
      (r_remove_min_rect f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> a2) ->
                    ((Tree a1) -> Key -> a1 -> (Tree a1) -> (Tree a1) -> Key
                    -> a1 -> (Tree a1) -> T -> () -> (Prod (Tree a1)
                    (Prod Key a1)) -> (R_remove_min a1) -> a2 -> (Tree 
                    a1) -> (Prod Key a1) -> () -> a2) -> (Tree a1) -> Key ->
                    a1 -> (Tree a1) -> (Prod (Tree a1) (Prod Key a1)) ->
                    (R_remove_min a1) -> a2
r_remove_min_rec =
  r_remove_min_rect

data R_merge elt =
   R_merge_0 (Tree elt) (Tree elt)
 | R_merge_1 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_merge_2 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree elt) 
 Key elt (Tree elt) T (Tree elt) (Prod Key elt) Key elt

r_merge_rect :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
                -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                -> (Tree a1) -> T -> () -> (Tree a1) -> Key -> a1 -> (Tree
                a1) -> T -> () -> (Tree a1) -> (Prod Key a1) -> () -> Key ->
                a1 -> () -> a2) -> (Tree a1) -> (Tree a1) -> (Tree a1) ->
                (R_merge a1) -> a2
r_merge_rect f f0 f1 _ _ _ r =
  case r of {
   R_merge_0 x x0 -> f x x0 __;
   R_merge_1 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_merge_2 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __}

r_merge_rec :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
               a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () ->
               a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1 ->
               (Tree a1) -> T -> () -> (Tree a1) -> Key -> a1 -> (Tree 
               a1) -> T -> () -> (Tree a1) -> (Prod Key a1) -> () -> Key ->
               a1 -> () -> a2) -> (Tree a1) -> (Tree a1) -> (Tree a1) ->
               (R_merge a1) -> a2
r_merge_rec =
  r_merge_rect

data R_remove0 elt =
   R_remove_4 (Tree elt)
 | R_remove_5 (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree elt) (R_remove0
                                                                    elt)
 | R_remove_6 (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_remove_7 (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree elt) (R_remove0
                                                                    elt)

r_remove_rect0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree 
                  a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () ->
                  (Tree a1) -> (R_remove0 a1) -> a2 -> a2) -> ((Tree 
                  a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
                  -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 ->
                  (Tree a1) -> T -> () -> () -> () -> (Tree a1) -> (R_remove0
                  a1) -> a2 -> a2) -> (Tree a1) -> (Tree a1) -> (R_remove0
                  a1) -> a2
r_remove_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_4 m -> f m __;
   R_remove_5 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect0 x f f0 f1 f2 l _res r1);
   R_remove_6 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_7 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1
      (r_remove_rect0 x f f0 f1 f2 r0 _res r1)}

r_remove_rec0 :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree 
                 a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () ->
                 (Tree a1) -> (R_remove0 a1) -> a2 -> a2) -> ((Tree a1) ->
                 (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> ()
                 -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree 
                 a1) -> T -> () -> () -> () -> (Tree a1) -> (R_remove0 
                 a1) -> a2 -> a2) -> (Tree a1) -> (Tree a1) -> (R_remove0 
                 a1) -> a2
r_remove_rec0 x =
  r_remove_rect0 x

data R_concat elt =
   R_concat_0 (Tree elt) (Tree elt)
 | R_concat_1 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_concat_2 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree
                                                                    elt) 
 Key elt (Tree elt) T (Tree elt) (Prod Key elt)

r_concat_rect :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                 a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
                 -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                 -> (Tree a1) -> T -> () -> (Tree a1) -> Key -> a1 -> (Tree
                 a1) -> T -> () -> (Tree a1) -> (Prod Key a1) -> () -> a2) ->
                 (Tree a1) -> (Tree a1) -> (Tree a1) -> (R_concat a1) -> a2
r_concat_rect f f0 f1 _ _ _ r =
  case r of {
   R_concat_0 x x0 -> f x x0 __;
   R_concat_1 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_concat_2 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __}

r_concat_rec :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
                -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                -> (Tree a1) -> T -> () -> (Tree a1) -> Key -> a1 -> (Tree
                a1) -> T -> () -> (Tree a1) -> (Prod Key a1) -> () -> a2) ->
                (Tree a1) -> (Tree a1) -> (Tree a1) -> (R_concat a1) -> a2
r_concat_rec =
  r_concat_rect

data R_split elt =
   R_split_0 (Tree elt)
 | R_split_1 (Tree elt) (Tree elt) Key elt (Tree elt) T (Triple elt) 
 (R_split elt) (Tree elt) (Option elt) (Tree elt)
 | R_split_2 (Tree elt) (Tree elt) Key elt (Tree elt) T
 | R_split_3 (Tree elt) (Tree elt) Key elt (Tree elt) T (Triple elt) 
 (R_split elt) (Tree elt) (Option elt) (Tree elt)

r_split_rect :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) ->
                Key -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Triple 
                a1) -> (R_split a1) -> a2 -> (Tree a1) -> (Option a1) ->
                (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key ->
                a1 -> (Tree a1) -> T -> () -> () -> () -> a2) -> ((Tree 
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () -> ()
                -> () -> (Triple a1) -> (R_split a1) -> a2 -> (Tree a1) ->
                (Option a1) -> (Tree a1) -> () -> a2) -> (Tree a1) -> (Triple
                a1) -> (R_split a1) -> a2
r_split_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_split_0 m -> f m __;
   R_split_1 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_2 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_3 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec :: N -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key
               -> a1 -> (Tree a1) -> T -> () -> () -> () -> (Triple a1) ->
               (R_split a1) -> a2 -> (Tree a1) -> (Option a1) -> (Tree 
               a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 ->
               (Tree a1) -> T -> () -> () -> () -> a2) -> ((Tree a1) -> (Tree
               a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> () ->
               (Triple a1) -> (R_split a1) -> a2 -> (Tree a1) -> (Option 
               a1) -> (Tree a1) -> () -> a2) -> (Tree a1) -> (Triple 
               a1) -> (R_split a1) -> a2
r_split_rec x =
  r_split_rect x

data R_map_option elt x =
   R_map_option_0 (Tree elt)
 | R_map_option_1 (Tree elt) (Tree elt) Key elt (Tree elt) T x (Tree x) 
 (R_map_option elt x) (Tree x) (R_map_option elt x)
 | R_map_option_2 (Tree elt) (Tree elt) Key elt (Tree elt) T (Tree x) 
 (R_map_option elt x) (Tree x) (R_map_option elt x)

r_map_option_rect :: (Key -> a1 -> Option a2) -> ((Tree a1) -> () -> a3) ->
                     ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T
                     -> () -> a2 -> () -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3
                     -> a3) -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree
                     a1) -> T -> () -> () -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3
                     -> a3) -> (Tree a1) -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3
r_map_option_rect f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_0 m -> f0 m __;
   R_map_option_1 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect f f0 f1 f2 r0 _res r2);
   R_map_option_2 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1 (r_map_option_rect f f0 f1 f2 l _res0 r1)
      _res r2 (r_map_option_rect f f0 f1 f2 r0 _res r2)}

r_map_option_rec :: (Key -> a1 -> Option a2) -> ((Tree a1) -> () -> a3) ->
                    ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T ->
                    () -> a2 -> () -> (Tree a2) -> (R_map_option a1 a2) -> a3
                    -> (Tree a2) -> (R_map_option a1 a2) -> a3 -> a3) ->
                    ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T ->
                    () -> () -> (Tree a2) -> (R_map_option a1 a2) -> a3 ->
                    (Tree a2) -> (R_map_option a1 a2) -> a3 -> a3) -> (Tree
                    a1) -> (Tree a2) -> (R_map_option a1 a2) -> a3
r_map_option_rec f =
  r_map_option_rect f

data R_map2_opt elt x0 x =
   R_map2_opt_0 (Tree elt) (Tree x0)
 | R_map2_opt_1 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T
 | R_map2_opt_2 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T 
 (Tree x0) Key x0 (Tree x0) T (Tree x0) (Option x0) (Tree x0) x (Tree x) 
 (R_map2_opt elt x0 x) (Tree x) (R_map2_opt elt x0 x)
 | R_map2_opt_3 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T 
 (Tree x0) Key x0 (Tree x0) T (Tree x0) (Option x0) (Tree x0) (Tree x) 
 (R_map2_opt elt x0 x) (Tree x) (R_map2_opt elt x0 x)

r_map2_opt_rect :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree 
                   a1) -> Tree a3) -> ((Tree a2) -> Tree a3) -> ((Tree 
                   a1) -> (Tree a2) -> () -> a4) -> ((Tree a1) -> (Tree 
                   a2) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T -> () ->
                   () -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree a1) -> Key
                   -> a1 -> (Tree a1) -> T -> () -> (Tree a2) -> Key -> a2 ->
                   (Tree a2) -> T -> () -> (Tree a2) -> (Option a2) -> (Tree
                   a2) -> () -> a3 -> () -> (Tree a3) -> (R_map2_opt 
                   a1 a2 a3) -> a4 -> (Tree a3) -> (R_map2_opt a1 a2 
                   a3) -> a4 -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree 
                   a1) -> Key -> a1 -> (Tree a1) -> T -> () -> (Tree 
                   a2) -> Key -> a2 -> (Tree a2) -> T -> () -> (Tree 
                   a2) -> (Option a2) -> (Tree a2) -> () -> () -> (Tree 
                   a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree a3) ->
                   (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree a1) -> (Tree
                   a2) -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4
r_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_0 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_1 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_2 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res
      r2 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_3 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree a1) ->
                  Tree a3) -> ((Tree a2) -> Tree a3) -> ((Tree a1) -> (Tree
                  a2) -> () -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree 
                  a1) -> Key -> a1 -> (Tree a1) -> T -> () -> () -> a4) ->
                  ((Tree a1) -> (Tree a2) -> (Tree a1) -> Key -> a1 -> (Tree
                  a1) -> T -> () -> (Tree a2) -> Key -> a2 -> (Tree a2) -> T
                  -> () -> (Tree a2) -> (Option a2) -> (Tree a2) -> () -> a3
                  -> () -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree
                  a3) -> (R_map2_opt a1 a2 a3) -> a4 -> a4) -> ((Tree 
                  a1) -> (Tree a2) -> (Tree a1) -> Key -> a1 -> (Tree 
                  a1) -> T -> () -> (Tree a2) -> Key -> a2 -> (Tree a2) -> T
                  -> () -> (Tree a2) -> (Option a2) -> (Tree a2) -> () -> ()
                  -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree 
                  a3) -> (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree 
                  a1) -> (Tree a2) -> (Tree a3) -> (R_map2_opt a1 a2 
                  a3) -> a4
r_map2_opt_rec f mapl mapr =
  r_map2_opt_rect f mapl mapr

fold' :: (Key -> a1 -> a2 -> a2) -> (Tree a1) -> a2 -> a2
fold' f s =
  fold0 f (elements s)

flatten_e :: (Enumeration a1) -> List (Prod Key a1)
flatten_e e =
  case e of {
   End -> Nil;
   More x e0 t r -> Cons (Pair x e0) (app (elements t) (flatten_e r))}

type Bst elt =
  Tree elt
  -- singleton inductive, whose constructor was Bst
  
this :: (Bst a1) -> Tree a1
this b =
  b

type T8 elt = Bst elt

type Key1 = N

empty1 :: T8 a1
empty1 =
  empty

is_empty1 :: (T8 a1) -> Bool
is_empty1 m =
  is_empty (this m)

add6 :: Key1 -> a1 -> (T8 a1) -> T8 a1
add6 x e m =
  add4 x e (this m)

remove1 :: Key1 -> (T8 a1) -> T8 a1
remove1 x m =
  remove x (this m)

mem1 :: Key1 -> (T8 a1) -> Bool
mem1 x m =
  mem x (this m)

find1 :: Key1 -> (T8 a1) -> Option a1
find1 x m =
  find x (this m)

map4 :: (a1 -> a2) -> (T8 a1) -> T8 a2
map4 f m =
  map0 f (this m)

mapi1 :: (Key1 -> a1 -> a2) -> (T8 a1) -> T8 a2
mapi1 f m =
  mapi f (this m)

map5 :: ((Option a1) -> (Option a2) -> Option a3) -> (T8 a1) -> (T8 a2) -> T8
        a3
map5 f m m' =
  map2 f (this m) (this m')

elements1 :: (T8 a1) -> List (Prod Key1 a1)
elements1 m =
  elements (this m)

cardinal0 :: (T8 a1) -> Nat
cardinal0 m =
  cardinal (this m)

fold1 :: (Key1 -> a1 -> a2 -> a2) -> (T8 a1) -> a2 -> a2
fold1 f m i =
  fold f (this m) i

equal1 :: (a1 -> a1 -> Bool) -> (T8 a1) -> (T8 a1) -> Bool
equal1 cmp m m' =
  equal cmp (this m) (this m')

type T9 = N

eq_dec7 :: N -> N -> Sumbool
eq_dec7 =
  eq_dec1

compare5 :: N -> N -> Comparison
compare5 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

type Elt = N

data Tree0 =
   Leaf0
 | Node0 T Tree0 N Tree0

empty2 :: Tree0
empty2 =
  Leaf0

is_empty2 :: Tree0 -> Bool
is_empty2 t =
  case t of {
   Leaf0 -> True;
   Node0 _ _ _ _ -> False}

mem2 :: N -> Tree0 -> Bool
mem2 x t =
  case t of {
   Leaf0 -> False;
   Node0 _ l k r ->
    case compare3 x k of {
     LT -> mem2 x l;
     EQ -> True;
     GT -> mem2 x r}}

min_elt :: Tree0 -> Option Elt
min_elt t =
  case t of {
   Leaf0 -> None;
   Node0 _ l x _ ->
    case l of {
     Leaf0 -> Some x;
     Node0 _ _ _ _ -> min_elt l}}

max_elt :: Tree0 -> Option Elt
max_elt t =
  case t of {
   Leaf0 -> None;
   Node0 _ _ x r ->
    case r of {
     Leaf0 -> Some x;
     Node0 _ _ _ _ -> max_elt r}}

choose :: Tree0 -> Option Elt
choose =
  min_elt

fold2 :: (Elt -> a1 -> a1) -> Tree0 -> a1 -> a1
fold2 f t base =
  case t of {
   Leaf0 -> base;
   Node0 _ l x r -> fold2 f r (f x (fold2 f l base))}

elements_aux0 :: (List N) -> Tree0 -> List N
elements_aux0 acc s =
  case s of {
   Leaf0 -> acc;
   Node0 _ l x r -> elements_aux0 (Cons x (elements_aux0 acc r)) l}

elements2 :: Tree0 -> List N
elements2 =
  elements_aux0 Nil

rev_elements_aux :: (List N) -> Tree0 -> List N
rev_elements_aux acc s =
  case s of {
   Leaf0 -> acc;
   Node0 _ l x r -> rev_elements_aux (Cons x (rev_elements_aux acc l)) r}

rev_elements :: Tree0 -> List N
rev_elements =
  rev_elements_aux Nil

cardinal1 :: Tree0 -> Nat
cardinal1 s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (add (cardinal1 l) (cardinal1 r))}

maxdepth :: Tree0 -> Nat
maxdepth s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (max (maxdepth l) (maxdepth r))}

mindepth :: Tree0 -> Nat
mindepth s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (min (mindepth l) (mindepth r))}

for_all :: (Elt -> Bool) -> Tree0 -> Bool
for_all f s =
  case s of {
   Leaf0 -> True;
   Node0 _ l x r ->
    case case f x of {
          True -> for_all f l;
          False -> False} of {
     True -> for_all f r;
     False -> False}}

exists_ :: (Elt -> Bool) -> Tree0 -> Bool
exists_ f s =
  case s of {
   Leaf0 -> False;
   Node0 _ l x r ->
    case case f x of {
          True -> True;
          False -> exists_ f l} of {
     True -> True;
     False -> exists_ f r}}

data Enumeration0 =
   End0
 | More0 Elt Tree0 Enumeration0

cons0 :: Tree0 -> Enumeration0 -> Enumeration0
cons0 s e =
  case s of {
   Leaf0 -> e;
   Node0 _ l x r -> cons0 l (More0 x r e)}

compare_more :: N -> (Enumeration0 -> Comparison) -> Enumeration0 ->
                Comparison
compare_more x1 cont e2 =
  case e2 of {
   End0 -> Gt;
   More0 x2 r2 e3 ->
    case compare3 x1 x2 of {
     LT -> Lt;
     EQ -> cont (cons0 r2 e3);
     GT -> Gt}}

compare_cont0 :: Tree0 -> (Enumeration0 -> Comparison) -> Enumeration0 ->
                 Comparison
compare_cont0 s1 cont e2 =
  case s1 of {
   Leaf0 -> cont e2;
   Node0 _ l1 x1 r1 ->
    compare_cont0 l1 (compare_more x1 (compare_cont0 r1 cont)) e2}

compare_end :: Enumeration0 -> Comparison
compare_end e2 =
  case e2 of {
   End0 -> Eq;
   More0 _ _ _ -> Lt}

compare6 :: Tree0 -> Tree0 -> Comparison
compare6 s1 s2 =
  compare_cont0 s1 compare_end (cons0 s2 End0)

equal2 :: Tree0 -> Tree0 -> Bool
equal2 s1 s2 =
  case compare6 s1 s2 of {
   Eq -> True;
   _ -> False}

subsetl :: (Tree0 -> Bool) -> N -> Tree0 -> Bool
subsetl subset_l1 x1 s2 =
  case s2 of {
   Leaf0 -> False;
   Node0 _ l2 x2 r2 ->
    case compare3 x1 x2 of {
     LT -> subsetl subset_l1 x1 l2;
     EQ -> subset_l1 l2;
     GT ->
      case mem2 x1 r2 of {
       True -> subset_l1 s2;
       False -> False}}}

subsetr :: (Tree0 -> Bool) -> N -> Tree0 -> Bool
subsetr subset_r1 x1 s2 =
  case s2 of {
   Leaf0 -> False;
   Node0 _ l2 x2 r2 ->
    case compare3 x1 x2 of {
     LT ->
      case mem2 x1 l2 of {
       True -> subset_r1 s2;
       False -> False};
     EQ -> subset_r1 r2;
     GT -> subsetr subset_r1 x1 r2}}

subset :: Tree0 -> Tree0 -> Bool
subset s1 s2 =
  case s1 of {
   Leaf0 -> True;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> False;
     Node0 _ l2 x2 r2 ->
      case compare3 x1 x2 of {
       LT ->
        case subsetl (subset l1) x1 l2 of {
         True -> subset r1 s2;
         False -> False};
       EQ ->
        case subset l1 l2 of {
         True -> subset r1 r2;
         False -> False};
       GT ->
        case subsetr (subset r1) x1 r2 of {
         True -> subset l1 s2;
         False -> False}}}}

type T10 = Tree0

height0 :: T10 -> T
height0 s =
  case s of {
   Leaf0 -> _0;
   Node0 h _ _ _ -> h}

singleton :: N -> Tree0
singleton x =
  Node0 _1 Leaf0 x Leaf0

create0 :: T10 -> N -> T10 -> Tree0
create0 l x r =
  Node0 (add2 (max2 (height0 l) (height0 r)) _1) l x r

assert_false0 :: T10 -> N -> T10 -> Tree0
assert_false0 =
  create0

bal0 :: T10 -> N -> T10 -> Tree0
bal0 l x r =
  let {hl = height0 l} in
  let {hr = height0 r} in
  case ltb0 (add2 hr _2) hl of {
   True ->
    case l of {
     Leaf0 -> assert_false0 l x r;
     Node0 _ ll lx lr ->
      case leb1 (height0 lr) (height0 ll) of {
       True -> create0 ll lx (create0 lr x r);
       False ->
        case lr of {
         Leaf0 -> assert_false0 l x r;
         Node0 _ lrl lrx lrr ->
          create0 (create0 ll lx lrl) lrx (create0 lrr x r)}}};
   False ->
    case ltb0 (add2 hl _2) hr of {
     True ->
      case r of {
       Leaf0 -> assert_false0 l x r;
       Node0 _ rl rx rr ->
        case leb1 (height0 rl) (height0 rr) of {
         True -> create0 (create0 l x rl) rx rr;
         False ->
          case rl of {
           Leaf0 -> assert_false0 l x r;
           Node0 _ rll rlx rlr ->
            create0 (create0 l x rll) rlx (create0 rlr rx rr)}}};
     False -> create0 l x r}}

add7 :: N -> Tree0 -> Tree0
add7 x s =
  case s of {
   Leaf0 -> Node0 _1 Leaf0 x Leaf0;
   Node0 h l y r ->
    case compare3 x y of {
     LT -> bal0 (add7 x l) y r;
     EQ -> Node0 h l y r;
     GT -> bal0 l y (add7 x r)}}

join0 :: Tree0 -> Elt -> T10 -> T10
join0 l =
  case l of {
   Leaf0 -> add7;
   Node0 lh ll lx lr -> (\x ->
    let {
     join_aux r =
       case r of {
        Leaf0 -> add7 x l;
        Node0 rh rl rx rr ->
         case ltb0 (add2 rh _2) lh of {
          True -> bal0 ll lx (join0 lr x r);
          False ->
           case ltb0 (add2 lh _2) rh of {
            True -> bal0 (join_aux rl) rx rr;
            False -> create0 l x r}}}}
    in join_aux)}

remove_min0 :: Tree0 -> Elt -> T10 -> Prod T10 Elt
remove_min0 l x r =
  case l of {
   Leaf0 -> Pair r x;
   Node0 _ ll lx lr ->
    case remove_min0 ll lx lr of {
     Pair l' m -> Pair (bal0 l' x r) m}}

merge0 :: Tree0 -> Tree0 -> Tree0
merge0 s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min0 l2 x2 r2 of {
       Pair s2' m -> bal0 s1 m s2'}}}

remove2 :: N -> Tree0 -> Tree0
remove2 x s =
  case s of {
   Leaf0 -> Leaf0;
   Node0 _ l y r ->
    case compare3 x y of {
     LT -> bal0 (remove2 x l) y r;
     EQ -> merge0 l r;
     GT -> bal0 l y (remove2 x r)}}

concat0 :: Tree0 -> Tree0 -> Tree0
concat0 s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min0 l2 x2 r2 of {
       Pair s2' m -> join0 s1 m s2'}}}

data Triple0 =
   Mktriple0 T10 Bool T10

t_left0 :: Triple0 -> T10
t_left0 t =
  case t of {
   Mktriple0 t_left1 _ _ -> t_left1}

t_in :: Triple0 -> Bool
t_in t =
  case t of {
   Mktriple0 _ t_in0 _ -> t_in0}

t_right0 :: Triple0 -> T10
t_right0 t =
  case t of {
   Mktriple0 _ _ t_right1 -> t_right1}

split0 :: N -> Tree0 -> Triple0
split0 x s =
  case s of {
   Leaf0 -> Mktriple0 Leaf0 False Leaf0;
   Node0 _ l y r ->
    case compare3 x y of {
     LT ->
      case split0 x l of {
       Mktriple0 ll b rl -> Mktriple0 ll b (join0 rl y r)};
     EQ -> Mktriple0 l True r;
     GT ->
      case split0 x r of {
       Mktriple0 rl b rr -> Mktriple0 (join0 l y rl) b rr}}}

inter :: Tree0 -> Tree0 -> Tree0
inter s1 s2 =
  case s1 of {
   Leaf0 -> Leaf0;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> Leaf0;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' pres r2' ->
        case pres of {
         True -> join0 (inter l1 l2') x1 (inter r1 r2');
         False -> concat0 (inter l1 l2') (inter r1 r2')}}}}

diff :: Tree0 -> Tree0 -> Tree0
diff s1 s2 =
  case s1 of {
   Leaf0 -> Leaf0;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' pres r2' ->
        case pres of {
         True -> concat0 (diff l1 l2') (diff r1 r2');
         False -> join0 (diff l1 l2') x1 (diff r1 r2')}}}}

union :: Tree0 -> Tree0 -> Tree0
union s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' _ r2' -> join0 (union l1 l2') x1 (union r1 r2')}}}

filter :: (Elt -> Bool) -> Tree0 -> Tree0
filter f s =
  case s of {
   Leaf0 -> Leaf0;
   Node0 _ l x r ->
    let {l' = filter f l} in
    let {r' = filter f r} in
    case f x of {
     True -> join0 l' x r';
     False -> concat0 l' r'}}

partition :: (Elt -> Bool) -> T10 -> Prod T10 T10
partition f s =
  case s of {
   Leaf0 -> Pair Leaf0 Leaf0;
   Node0 _ l x r ->
    case partition f l of {
     Pair l1 l2 ->
      case partition f r of {
       Pair r1 r2 ->
        case f x of {
         True -> Pair (join0 l1 x r1) (concat0 l2 r2);
         False -> Pair (concat0 l1 r1) (join0 l2 x r2)}}}}

ltb_tree :: N -> Tree0 -> Bool
ltb_tree x s =
  case s of {
   Leaf0 -> True;
   Node0 _ l y r ->
    case compare3 x y of {
     GT -> andb (ltb_tree x l) (ltb_tree x r);
     _ -> False}}

gtb_tree :: N -> Tree0 -> Bool
gtb_tree x s =
  case s of {
   Leaf0 -> True;
   Node0 _ l y r ->
    case compare3 x y of {
     LT -> andb (gtb_tree x l) (gtb_tree x r);
     _ -> False}}

isok :: Tree0 -> Bool
isok s =
  case s of {
   Leaf0 -> True;
   Node0 _ l x r ->
    andb (andb (andb (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)}

type T11 = N

compare7 :: N -> N -> Comparison
compare7 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec8 :: N -> N -> Sumbool
eq_dec8 =
  eq_dec7

type T12 = N

compare8 :: N -> N -> Comparison
compare8 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec9 :: N -> N -> Sumbool
eq_dec9 =
  eq_dec8

eq_dec10 :: N -> N -> Sumbool
eq_dec10 =
  eq_dec7

lt_dec3 :: N -> N -> Sumbool
lt_dec3 x y =
  let {
   c = compSpec2Type x y
         (case compare3 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb5 :: N -> N -> Bool
eqb5 x y =
  case eq_dec10 x y of {
   Left -> True;
   Right -> False}

data R_min_elt =
   R_min_elt_0 Tree0
 | R_min_elt_1 Tree0 T Tree0 N Tree0
 | R_min_elt_2 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 (Option Elt) R_min_elt

data R_max_elt =
   R_max_elt_0 Tree0
 | R_max_elt_1 Tree0 T Tree0 N Tree0
 | R_max_elt_2 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 (Option Elt) R_max_elt

type T13 = N

compare9 :: N -> N -> Comparison
compare9 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec11 :: N -> N -> Sumbool
eq_dec11 =
  eq_dec7

type T14 = N

compare10 :: N -> N -> Comparison
compare10 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec12 :: N -> N -> Sumbool
eq_dec12 =
  eq_dec11

eq_dec13 :: N -> N -> Sumbool
eq_dec13 =
  eq_dec7

lt_dec4 :: N -> N -> Sumbool
lt_dec4 x y =
  let {
   c = compSpec2Type x y
         (case compare3 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb6 :: N -> N -> Bool
eqb6 x y =
  case eq_dec13 x y of {
   Left -> True;
   Right -> False}

flatten_e0 :: Enumeration0 -> List Elt
flatten_e0 e =
  case e of {
   End0 -> Nil;
   More0 x t r -> Cons x (app (elements2 t) (flatten_e0 r))}

data R_bal0 =
   R_bal_9 T10 N T10
 | R_bal_10 T10 N T10 T Tree0 N Tree0
 | R_bal_11 T10 N T10 T Tree0 N Tree0
 | R_bal_12 T10 N T10 T Tree0 N Tree0 T Tree0 N Tree0
 | R_bal_13 T10 N T10
 | R_bal_14 T10 N T10 T Tree0 N Tree0
 | R_bal_15 T10 N T10 T Tree0 N Tree0
 | R_bal_16 T10 N T10 T Tree0 N Tree0 T Tree0 N Tree0
 | R_bal_17 T10 N T10

data R_remove_min0 =
   R_remove_min_2 Tree0 Elt T10
 | R_remove_min_3 Tree0 Elt T10 T Tree0 N Tree0 (Prod T10 Elt) R_remove_min0 
 T10 Elt

data R_merge0 =
   R_merge_3 Tree0 Tree0
 | R_merge_4 Tree0 Tree0 T Tree0 N Tree0
 | R_merge_5 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Elt

data R_concat0 =
   R_concat_3 Tree0 Tree0
 | R_concat_4 Tree0 Tree0 T Tree0 N Tree0
 | R_concat_5 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Elt

data R_inter =
   R_inter_0 Tree0 Tree0
 | R_inter_1 Tree0 Tree0 T Tree0 N Tree0
 | R_inter_2 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Bool T10 
 Tree0 R_inter Tree0 R_inter
 | R_inter_3 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Bool T10 
 Tree0 R_inter Tree0 R_inter

data R_diff =
   R_diff_0 Tree0 Tree0
 | R_diff_1 Tree0 Tree0 T Tree0 N Tree0
 | R_diff_2 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Bool T10 
 Tree0 R_diff Tree0 R_diff
 | R_diff_3 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Bool T10 
 Tree0 R_diff Tree0 R_diff

data R_union =
   R_union_0 Tree0 Tree0
 | R_union_1 Tree0 Tree0 T Tree0 N Tree0
 | R_union_2 Tree0 Tree0 T Tree0 N Tree0 T Tree0 N Tree0 T10 Bool T10 
 Tree0 R_union Tree0 R_union

type T15 = N

compare11 :: N -> N -> Comparison
compare11 x y =
  case compare3 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec14 :: N -> N -> Sumbool
eq_dec14 =
  eq_dec7

type Elt0 = N

type T_ =
  T10
  -- singleton inductive, whose constructor was Mkt
  
this0 :: T_ -> T10
this0 t =
  t

type T16 = T_

mem3 :: Elt0 -> T16 -> Bool
mem3 x s =
  mem2 x (this0 s)

add8 :: Elt0 -> T16 -> T16
add8 x s =
  add7 x (this0 s)

remove3 :: Elt0 -> T16 -> T16
remove3 x s =
  remove2 x (this0 s)

singleton0 :: Elt0 -> T16
singleton0 x =
  singleton x

union0 :: T16 -> T16 -> T16
union0 s s' =
  union (this0 s) (this0 s')

inter0 :: T16 -> T16 -> T16
inter0 s s' =
  inter (this0 s) (this0 s')

diff0 :: T16 -> T16 -> T16
diff0 s s' =
  diff (this0 s) (this0 s')

equal3 :: T16 -> T16 -> Bool
equal3 s s' =
  equal2 (this0 s) (this0 s')

subset0 :: T16 -> T16 -> Bool
subset0 s s' =
  subset (this0 s) (this0 s')

empty3 :: T16
empty3 =
  empty2

is_empty3 :: T16 -> Bool
is_empty3 s =
  is_empty2 (this0 s)

elements3 :: T16 -> List Elt0
elements3 s =
  elements2 (this0 s)

choose0 :: T16 -> Option Elt0
choose0 s =
  choose (this0 s)

fold3 :: (Elt0 -> a1 -> a1) -> T16 -> a1 -> a1
fold3 f s =
  fold2 f (this0 s)

cardinal2 :: T16 -> Nat
cardinal2 s =
  cardinal1 (this0 s)

filter0 :: (Elt0 -> Bool) -> T16 -> T16
filter0 f s =
  filter f (this0 s)

for_all0 :: (Elt0 -> Bool) -> T16 -> Bool
for_all0 f s =
  for_all f (this0 s)

exists_0 :: (Elt0 -> Bool) -> T16 -> Bool
exists_0 f s =
  exists_ f (this0 s)

partition0 :: (Elt0 -> Bool) -> T16 -> Prod T16 T16
partition0 f s =
  let {p = partition f (this0 s)} in Pair (fst p) (snd p)

eq_dec15 :: T16 -> T16 -> Sumbool
eq_dec15 s0 s'0 =
  let {b = equal2 s0 s'0} in
  case b of {
   True -> Left;
   False -> Right}

compare12 :: T16 -> T16 -> Comparison
compare12 s s' =
  compare6 (this0 s) (this0 s')

min_elt0 :: T16 -> Option Elt0
min_elt0 s =
  min_elt (this0 s)

max_elt0 :: T16 -> Option Elt0
max_elt0 s =
  max_elt (this0 s)

type Elt1 = N

type T17 = T16

empty4 :: T17
empty4 =
  empty3

is_empty4 :: T17 -> Bool
is_empty4 =
  is_empty3

mem4 :: Elt1 -> T17 -> Bool
mem4 =
  mem3

add9 :: Elt1 -> T17 -> T17
add9 =
  add8

singleton1 :: Elt1 -> T17
singleton1 =
  singleton0

remove4 :: Elt1 -> T17 -> T17
remove4 =
  remove3

union1 :: T17 -> T17 -> T17
union1 =
  union0

inter1 :: T17 -> T17 -> T17
inter1 =
  inter0

diff1 :: T17 -> T17 -> T17
diff1 =
  diff0

eq_dec16 :: T17 -> T17 -> Sumbool
eq_dec16 =
  eq_dec15

equal4 :: T17 -> T17 -> Bool
equal4 =
  equal3

subset1 :: T17 -> T17 -> Bool
subset1 =
  subset0

fold4 :: (Elt1 -> a1 -> a1) -> T17 -> a1 -> a1
fold4 x x0 x1 =
  fold3 x x0 x1

for_all1 :: (Elt1 -> Bool) -> T17 -> Bool
for_all1 =
  for_all0

exists_1 :: (Elt1 -> Bool) -> T17 -> Bool
exists_1 =
  exists_0

filter1 :: (Elt1 -> Bool) -> T17 -> T17
filter1 =
  filter0

partition1 :: (Elt1 -> Bool) -> T17 -> Prod T17 T17
partition1 =
  partition0

cardinal3 :: T17 -> Nat
cardinal3 =
  cardinal2

elements4 :: T17 -> List Elt1
elements4 =
  elements3

choose1 :: T17 -> Option Elt1
choose1 =
  choose0

eqb7 :: N -> N -> Bool
eqb7 x y =
  case eq_dec14 x y of {
   Left -> True;
   Right -> False}

min_elt1 :: T17 -> Option Elt1
min_elt1 =
  min_elt0

max_elt1 :: T17 -> Option Elt1
max_elt1 =
  max_elt0

compare13 :: T17 -> T17 -> Compare T17
compare13 s s' =
  let {c = compSpec2Type s s' (compare12 s s')} in
  case c of {
   CompEqT -> EQ;
   CompLtT -> LT;
   CompGtT -> GT}

type T18 = N

compare14 :: N -> N -> Compare N
compare14 =
  compare3

eq_dec17 :: N -> N -> Sumbool
eq_dec17 =
  eq_dec1

data Image =
   MkImage String N

filename :: Image -> String
filename i =
  case i of {
   MkImage filename0 _ -> filename0}

timestamp :: Image -> N
timestamp i =
  case i of {
   MkImage _ timestamp0 -> timestamp0}

type ImageId = N

type CategoryId = N

type Index = T17

data ImageDb =
   MkDb (T8 Image) (T8 Index) ImageId

images :: ImageDb -> T8 Image
images i =
  case i of {
   MkDb images0 _ _ -> images0}

indices :: ImageDb -> T8 Index
indices i =
  case i of {
   MkDb _ indices0 _ -> indices0}

next_id :: ImageDb -> ImageId
next_id i =
  case i of {
   MkDb _ _ next_id0 -> next_id0}

newDb :: ImageDb
newDb =
  MkDb empty1 empty1 zero

create_image :: ImageDb -> Image -> ImageDb
create_image db img =
  MkDb (add6 (next_id db) img (images db)) (indices db) (succ0 (next_id db))

find_category_ids :: ImageDb -> CategoryId -> Index
find_category_ids db cat =
  case find1 cat (indices db) of {
   Some xs -> xs;
   None -> empty4}

set_from_list :: (List N) -> Index
set_from_list xs =
  fold_right add9 empty4 xs

list_from_set :: Index -> List N
list_from_set xs =
  fold4 (\x x0 -> Cons x x0) xs Nil

find_categories_ids :: ImageDb -> (List CategoryId) -> Index
find_categories_ids db categories =
  case categories of {
   Nil -> set_from_list (map fst (elements1 (images db)));
   Cons cat cats ->
    inter1 (find_category_ids db cat) (find_categories_ids db cats)}

find_imgs :: ImageDb -> (List ImageId) -> List Image
find_imgs db imgs =
  case imgs of {
   Nil -> Nil;
   Cons i is ->
    case find1 i (images db) of {
     Some img -> Cons img (find_imgs db is);
     None -> find_imgs db is}}

find_categories :: ImageDb -> (List CategoryId) -> List Image
find_categories db categories =
  find_imgs db (list_from_set (find_categories_ids db categories))

delete_image :: ImageDb -> ImageId -> ImageDb
delete_image db img =
  MkDb (remove1 img (images db)) (map4 (remove4 img) (indices db))
    (next_id db)

tag_image :: ImageDb -> ImageId -> CategoryId -> ImageDb
tag_image db img cat =
  let {
   idxs = case find1 cat (indices db) of {
           Some idx -> add6 cat (add9 img idx) (indices db);
           None -> add6 cat (singleton1 img) (indices db)}}
  in
  MkDb (images db) idxs (next_id db)

untag_image :: ImageDb -> ImageId -> CategoryId -> ImageDb
untag_image db img cat =
  let {
   idxs = case find1 cat (indices db) of {
           Some idx -> add6 cat (remove4 img idx) (indices db);
           None -> indices db}}
  in
  MkDb (images db) idxs (next_id db)

num_images :: ImageDb -> Nat
num_images db =
  cardinal0 (images db)

mem_image :: ImageDb -> ImageId -> Bool
mem_image db img =
  mem1 img (images db)

