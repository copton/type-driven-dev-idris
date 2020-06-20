module Main

import Data.Primitives.Views

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223
  in (seed' `shiftR` 2) :: randoms seed'

boundedRandoms : Int -> Stream Int
boundedRandoms seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12) -- ??? Why are we working with any views and proofs here at all?
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

every_other : Stream a -> Stream a
every_other (value :: _ :: xs) = value :: every_other xs

data InfList : Type -> Type where
  (::) : a -> Inf (InfList a) -> InfList a

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

implementation Functor InfList where
  map f (x :: xs) = f x :: map f xs

getPrefix : Nat -> InfList a -> List a
getPrefix Z _ = []
getPrefix (S n) (x :: xs) = x :: getPrefix n xs

data Face = Head | Tails

mapFace' : Int -> Face
mapFace' x with (divides x 2)
  mapFace' ((2 * div) + rem) | (DivBy prf) =
    case rem of
      0 => Head
      1 => Tails

-- ??? what would it take to make this function total without assertion?
total
mapFace : Int -> Face
mapFace x = assert_total $ mapFace' x


total
coinFlips : Nat -> Stream Int -> List Face
coinFlips n s = take n (map mapFace s)

square_root_approx : (number: Double) -> (approx: Double) -> Stream Double
square_root_approx number approx =
  let next = (approx + (number / approx)) / 2 in
  next :: square_root_approx number next

square_root_bound : (max: Nat)
                 -> (number: Double)
                 -> (bound : Double)
                 -> (approxs : Stream Double)
                 -> Double
square_root_bound Z _ _ (x :: xs) = x
square_root_bound (S k) number bound (x :: xs) =
  let val = x * x in
  if abs (number - val) < bound
    then x
    else square_root_bound k number bound xs

square_root : (number: Double) -> Double
square_root number =
  square_root_bound 100 number 0.0000000001 (square_root_approx number number)
