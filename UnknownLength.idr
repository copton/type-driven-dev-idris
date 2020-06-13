module Main

data MyVect : (n : Nat) -> Type -> Type where
  MyNil : MyVect Z a
  MyCons : a -> MyVect n a -> MyVect (S n) a

implementation Show a => Show (MyVect n a) where
  show MyNil = "[]"
  show (MyCons x xs) = show x ++ ", " ++ show xs

{-
decEq : DecEq t => (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

Data type Prelude.Basics.Dec : Type -> Type
    Decidability. A decidable property either holds or is a contradiction.

Constructors:
    Yes : (prf : prop) -> Dec prop
        The case where the property holds
        Arguments:
            prf : prop  -- the proof

    No : (contra : prop -> Void) -> Dec prop
        The case where the property holding would be a contradiction
        Arguments:
            contra : prop -> Void  -- a demonstration that prop would be a
            contradiction

implementation DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq Z     (S _) = No ZnotS
  decEq (S _) Z     = No (negEqSym ZnotS)
  decEq (S n) (S m) with (decEq n m)
    | Yes p = Yes $ cong p
    | No p = No $ \h : (S n = S m) => p $ succInjective n m h
-}

headUnequal : DecEq a
          => {xs : MyVect n a} -> {ys : MyVect n a}
          -> ((x = y) -> Void)
          -> (((MyCons x xs) = (MyCons y ys)) -> Void)
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a
             => {xs : MyVect n a} -> {ys : MyVect n a}
             -> ((xs = ys) -> Void)
             -> (((MyCons x xs) = (MyCons y ys)) -> Void)
tailUnequal contra Refl = contra Refl

implementation DecEq a => DecEq (MyVect n a) where
  decEq MyNil MyNil = Yes Refl
  decEq (MyCons x xs) (MyCons y ys) =
    case decEq x y of
      Yes Refl => case decEq xs ys of
        Yes Refl => Yes Refl
        No contra => No (tailUnequal contra)
      No contra => No (headUnequal contra)

replicate  : (n : Nat) -> (x : a) -> MyVect n a
replicate Z x = MyNil
replicate (S k) x = MyCons x (replicate k x)

zip : {n : Nat} -> MyVect n a -> MyVect n b -> MyVect n (a, b)
zip MyNil MyNil = MyNil
zip (MyCons x xs) (MyCons y ys) = MyCons (x, y) (zip xs ys)

exactLength : {m : Nat} -> (n : Nat) -> MyVect m a -> Maybe (MyVect n a)
exactLength {m} n v = case decEq m n of
  Yes Refl => Just v
  No _ => Nothing

parse : String -> (n : Nat ** MyVect n Int)
parse s =
  let n = length s
  in (n ** replicate n 1)

main : IO ()
main = do
  s1 <- getLine
  let (n1 ** v1) = parse s1
  s2 <- getLine
  let (n2 ** v2) = parse s2
  case exactLength n1 v2 of
    Nothing => putStrLn "no match"
    Just v2' => printLn (zip v1 v2')
  pure ()
