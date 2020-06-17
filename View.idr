module Main


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
takeN Z _             = Exact []  -- ??? how is the implicit parameter `rest` being inferred?
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

data SnocList : List a -> Type where
  SEmpty : SnocList []
  Snoc  : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : (snoc: SnocList acc) -> (rest: List a) -> SnocList (acc ++ rest)
snocListHelp {acc} snoc [] = rewrite appendNilRightNeutral acc in snoc
snocListHelp {acc} snoc (x :: xs) =
  rewrite appendAssociative acc [x] xs
  in snocListHelp (Snoc snoc {x}) xs

total
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp SEmpty xs

total
myReverseHelper : (input: List a) -> SnocList input -> List a
myReverseHelper []          SEmpty     = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

total
myReverse : List a -> List a
myReverse input = myReverseHelper input (snocList input)

total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | SEmpty = True
  isSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc xsrec) | SEmpty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      case x == y of
        True => isSuffix xs ys | xsrec | ysrec
        False => False
