import Data.Vect

pali : Nat -> String -> Bool
pali l x =
  if length x < l
    then False
    else
      let y = toLower x in
      reverse y == y

counts : String -> (Nat, Nat)
counts s = (length s, length $ words s)

top_ten : Ord a => List a -> List a
top_ten = Prelude.List.take 10 . reverse . sort

over_length : Nat -> List String -> Nat
over_length l = length . filter ((> l) . length)

lal : Num a => List a -> a
lal xs = sum xs

allLengths : List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not (isEven k)

allLen : Vect n String -> Vect n Nat
allLen [] = []
allLen (x :: xs) = length x :: allLen xs

insertSorted : Ord a => a -> Vect len a -> Vect (S len) a
insertSorted x [] = [x]
insertSorted x (y :: ys) =
  if x < y
    then x :: y :: ys
    else y :: insertSorted x ys

total vSort : Ord a => Vect n a -> Vect n a
vSort [] = []
vSort (x :: xs) =
  let xs' = vSort xs
  in insertSorted x xs'

total vTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vTake Z [] = []
vTake Z (x :: xs) = []
vTake (S k) (x :: xs) = x :: vTake k xs

myLength : List a -> Nat
myLength [] = 0
myLength (x :: xs) = 1 + myLength xs

myReverse : List a -> List a
myReverse [] = []
myReverse (x :: xs) = myReverse xs ++ [x]

myMap : (a -> b) -> List a -> List b
myMap _ [] = []
myMap f (x :: xs) = f x :: myMap f xs

myMapV : (a -> b) -> Vect n a -> Vect n b
myMapV _ [] = []
myMapV f (x :: xs) = f x :: myMapV f xs

total tranposeMat : Vect m (Vect n a) -> Vect n (Vect m a)
tranposeMat [] = replicate _ []
tranposeMat (x :: xs) = zipWith (::) x $ tranposeMat xs

total addVec : Num a => Vect n a -> Vect n a -> Vect n a
addVec [] [] = []
addVec (x :: xs) (y :: ys) = (x + y) :: addVec xs ys

total addMatrix : Num a => Vect m (Vect n a) -> Vect m (Vect n a) -> Vect m (Vect n a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = addVec x y :: addMatrix xs ys

data T = A | B

data D : T -> Type where
  Opt1 : D A
  Opt2 : Int -> D B

imp : D A -> Int
imp Opt1 = 23
imp (Opt2 _) impossible
