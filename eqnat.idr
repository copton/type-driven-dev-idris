module Main

import Data.Vect

data EqNat : (m : Nat) -> (n : Nat) -> Type where
  Same : (k : Nat) -> EqNat k k

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

checkEqNat : (m : Nat) -> (n : Nat) -> Maybe (EqNat m n)
checkEqNat Z Z = Just $ Same Z
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
  Nothing => Nothing
  Just eq => Just $ sameS _ _ eq

total same_cons : {x : a} -> {xs : List a} -> {ys : List a}
        -> xs = ys -> x :: xs = x :: ys
same_cons p = cong p

total same_lists : {x : a} -> {y : a} -> {xs : List a} -> {ys : List a}
               -> x = y
               -> xs = ys
               -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : (a : Nat) -> (b : Nat) -> (c : Nat) -> Type where
  Same3 : (a : Nat) -> ThreeEq a a a

total allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (Same3 z) = Same3 (S z)

zeroNotSuc : (S k = 0) -> Void
zeroNotSuc Refl impossible

sucNotZero : (0 = S k) -> Void
sucNotZero Refl impossible

noRec : (contra : (j = k) -> Void) -> (S j = S k) -> Void
noRec contra Refl = contra Refl

checkEqNat' : (m : Nat) -> (n : Nat) -> Dec (n = m)
checkEqNat' Z Z = Yes Refl
checkEqNat' Z (S k) = No zeroNotSuc
checkEqNat' (S k) Z = No sucNotZero
checkEqNat' (S k) (S j) = case checkEqNat' k j of
  No contra => No (noRec contra)
  Yes prf   => Yes (cong prf)

headUnequal : DecEq a
          => {xs : Vect n a}
          -> {ys : Vect n a}
          -> (contra : (x = y) -> Void)
          -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a
             => {xs : Vect n a}
             -> {ys : Vect n a}
             -> (contra : (xs = ys) -> Void)
             -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl
