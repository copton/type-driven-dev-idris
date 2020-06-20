module Main

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
    Empty => NonEmpty [] x
    NonEmpty ys y => NonEmpty (x :: ys) y

describeHelper : (input : List Int) -> ListLast input -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) =
  "Non-empty, initial portion = " ++ show xs

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

describeListEnd' : List Int -> String
describeListEnd' input with (listLast input)
  describeListEnd' []          | Empty           = "Empty"
  describeListEnd' (xs ++ [x]) | (NonEmpty xs x) =
    "Non-empty, initial portion = " ++ show xs

data SplitList : List a -> Type where
  SplitNone : SplitList []
  SplitOne  : SplitList [x]
  SplitPair : (xs : List a) -> (ys : List a) -> SplitList (xs ++ ys)

total
splitList : (input : List a) -> SplitList input
splitList input = go input input
  where
    go _ [] = SplitNone
    go _ [x] = SplitOne
    go (_ :: _ :: counter) (item :: items) =
      case go counter items of
        SplitNone => SplitOne
        SplitOne {x} => SplitPair [item] [x]
        (SplitPair left right) =>
          SplitPair (item :: left) right
    go _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort []                | SplitNone                = []
  mergeSort (x :: [])         | SplitOne                 = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) =
    merge (mergeSort lefts) (mergeSort rights)

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z _             = Exact []
takeN (S k) []        = Fewer
takeN (S k) (x :: xs) =
  case takeN k xs of
    Exact ys => Exact (x :: ys)
    Fewer    => Fewer

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs             | Fewer        = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) =
    n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves lst = halves' (length lst `div` 2) lst
  where
    halves' n xs with (takeN n xs)
      halves' n xs             | Fewer = (xs, []) -- ??? Actually impossible case, can we avoid this?
      halves' n (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

data MySnocList : List a -> Type where
  SEmpty : MySnocList []
  Snoc  : (rec : MySnocList xs) -> MySnocList (xs ++ [x])

snocListHelp : (snoc: MySnocList acc) -> (rest: List a) -> MySnocList (acc ++ rest)
snocListHelp {acc} snoc [] = rewrite appendNilRightNeutral acc in snoc
snocListHelp {acc} snoc (x :: xs) =
  rewrite appendAssociative acc [x] xs
  in snocListHelp (Snoc snoc {x}) xs

total
mySnocList : (xs : List a) -> MySnocList xs
mySnocList xs = snocListHelp SEmpty xs

total
myReverseHelper : (input: List a) -> MySnocList input -> List a
myReverseHelper []          SEmpty     = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

total
myReverse : List a -> List a
myReverse input = myReverseHelper input (mySnocList input)

total
myIsSuffix : Eq a => List a -> List a -> Bool
myIsSuffix input1 input2 with (mySnocList input1)
  myIsSuffix [] input2 | SEmpty = True
  myIsSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (mySnocList input2)
    myIsSuffix (xs ++ [x]) [] | (Snoc xsrec) | SEmpty = False
    myIsSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      case x == y of
        True => myIsSuffix xs ys | xsrec | ysrec
        False => False

total
mergeSortTotal : Ord a => List a -> List a
mergeSortTotal input with (splitRec input)
  mergeSortTotal [] | SplitRecNil = []
  mergeSortTotal [x] | SplitRecOne = [x]
  mergeSortTotal (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (mergeSortTotal lefts | lrec) (mergeSortTotal rights | rrec)

total
equalSuffix' : Eq a => List a -> List a -> List a
equalSuffix' lhs rhs with (snocList lhs)
  equalSuffix' [] rhs | Empty = []
  equalSuffix' (xs ++ [x]) rhs | (Snoc lhs_rec) with (snocList rhs)
    equalSuffix' (xs ++ [x]) [] | (Snoc lhs_rec) | Empty = []
    equalSuffix' (xs ++ [x]) (ys ++ [y]) | (Snoc lhs_rec) | (Snoc rhs_rec) =
      case x == y of
        True => x :: equalSuffix' xs ys | lhs_rec | rhs_rec
        False => []

total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix lhs rhs = reverse (equalSuffix' lhs rhs)

total
mergeVect : Ord a => Vect n a -> Vect m a -> Vect (n + m) a
mergeVect [] [] = []
mergeVect [] xs = xs
mergeVect {n} xs [] = rewrite plusZeroRightNeutral n in xs
mergeVect {n = S k} {m = S l} lhs@(x :: xs) rhs@(y :: ys) =
  case x < y of
    True  => x :: mergeVect xs rhs
    False =>
      rewrite sym (plusSuccRightSucc k l) in
      y :: mergeVect lhs ys

total
mergeSortVect : Ord a => Vect n a -> Vect n a
mergeSortVect input with (Data.Vect.Views.splitRec input)
  mergeSortVect [] | SplitRecNil = []
  mergeSortVect [x] | SplitRecOne = [x]
  mergeSortVect (xs ++ ys) | (SplitRecPair lrec rrec) =
    mergeVect (mergeSortVect xs | lrec) (mergeSortVect ys | rrec)

total
toBinary' : Nat -> List Char
toBinary' k with (halfRec k)
  toBinary' Z           | HalfRecZ          = []
  toBinary' (n + n)     | (HalfRecEven rec) = '0' :: (toBinary' n | rec)
  toBinary' (S (n + n)) | (HalfRecOdd rec)  = '1' :: (toBinary' n | rec)

total
toBinary : Nat -> String
toBinary k = pack $ reverse $ toBinary' k
{- ??? `toBinary 42` runs forever, due to `halfRec`
"My first instinct would be to modify Half to return a number + a lazy proof
it's the right one instead of having the view as is". This is puzzling, I
thought proofs are being evaluated at compile time, so having a proof being lazy
made little sense in my mind.
-}

total
palindrom : List Char -> Bool
palindrom input with (vList input)
  palindrom [] | VNil = True
  palindrom [x] | VOne = True
  palindrom (x :: (xs ++ [y])) | (VCons rec) =
    case x == y of
      False => False
      True => palindrom xs | rec
