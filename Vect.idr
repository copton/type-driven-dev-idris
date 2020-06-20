module Main

data MyVect : (n : Nat) -> Type -> Type where
  MyNil : MyVect Z a
  MyCons : a -> MyVect n a -> MyVect (S n) a

total append : MyVect n a -> MyVect m a -> MyVect (n + m) a
append MyNil v2      = v2
append (MyCons x xs) v2 = MyCons x (append xs v2)

myReverse : MyVect n a -> MyVect n a
myReverse MyNil = MyNil
myReverse (MyCons x xs) = prf (myReverse xs `append` MyCons x MyNil)
  where
    prf : {k : Nat} -> MyVect (k + 1) a -> MyVect (S k) a
    prf {k} result = rewrite plusCommutative 1 k in result

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z Z = Refl
myPlusCommutes Z (S k) = rewrite sym (plusZeroRightNeutral k) in Refl
myPlusCommutes (S k) Z = rewrite sym (plusZeroRightNeutral k) in Refl
myPlusCommutes (S k) (S j) =
  let recProof = myPlusCommutes k j in
  rewrite sym (plusSuccRightSucc k j) in
  rewrite sym (plusSuccRightSucc j k) in
  rewrite recProof in Refl

reverse' : {n : Nat} -> {m : Nat} -> MyVect n a -> MyVect m a -> MyVect (n + m) a
reverse' {n} {m=Z}   acc MyNil        = rewrite plusZeroRightNeutral n in acc
reverse' {n} {m=S k} acc (MyCons h t) =
  rewrite sym (plusSuccRightSucc n k)
  in reverse' (MyCons h acc) t

myReverseFast : MyVect n a -> MyVect n a
myReverseFast xs = reverse' MyNil xs

headUnequal : DecEq a
          => {xs : MyVect n a}
          -> {ys : MyVect n a}
          -> (contra : (x = y) -> Void)
          -> ((MyCons x xs) = (MyCons y ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a
             => {xs : MyVect n a}
             -> {ys : MyVect n a}
             -> (contra : (xs = ys) -> Void)
             -> ((MyCons x xs) = (MyCons y ys)) -> Void
tailUnequal contra Refl = contra Refl

implementation DecEq a => DecEq (MyVect n a) where
  decEq MyNil MyNil = Yes Refl
  decEq (MyCons x xs) (MyCons y ys) =
    case decEq xs ys of
      No contra => No $ tailUnequal contra
      Yes Refl =>
        case decEq x y of
          No contra => No $ headUnequal contra
          Yes Refl => Yes Refl

data MyElem : a -> MyVect k a -> Type where
  MyHere : MyElem x (MyCons x xs)
  MyThere : (later : MyElem x xs) -> MyElem x (MyCons y xs)

implementation Uninhabited (MyElem x MyNil) where
  uninhabited _ impossible

removeElem : (value : a)
          -> (xs : MyVect (S n) a)
          -> (prf : MyElem value xs)
          -> MyVect n a
removeElem value (MyCons value xs) MyHere = xs
removeElem {n = Z} value (MyCons y MyNil) (MyThere later)= absurd later
removeElem {n = S k} value (MyCons x xs) (MyThere later) = MyCons x $ removeElem value xs later
