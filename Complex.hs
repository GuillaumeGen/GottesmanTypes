{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Complex where

import Bool
import Nat
import Int
import Rational
import Pair
import List

-- We do not represent the full set of complex numbers,
-- only Q[i,sqrt(2),sqrt(3),...].
-- The element of `C` `[(q1,[]),(q2,[a]),(q3,[b]),(q4,[c,d])]` is
-- q1 + q2√a + q3√b + q4√c√d.
-- For computational reason, we decompose the number under the square root as a list
-- of prime numbers (or -1), to avoid doing prime factorisation,
-- which is a costly operation.
-- We assume that there are no redundancies in the lists and they are all sorted.
-- So the list behind the square root is sorted and the main list is sorted
-- and the main list is sorted alphabetically by square roots.
type C = [(Q, [Z])]

type IsC = IsList (IsPair IsQ (IsList IsZ))

multIsC :: IsC a -> IsC b -> IsC (MultC a b)
multIsC = undefined

type family IsNullC (x :: C) :: Bool where
  IsNullC '[] = 'True
  IsNullC ('(,) q _ ': tl) =
    IsNullCAux (IsNullQ q) tl
type family IsNullCAux (b :: Bool) (c :: C) :: Bool where
  IsNullCAux 'True c = IsNullC c
  IsNullCAux 'False _ = 'False

type family EqC (a :: C) (b :: C) :: Bool where
  EqC '[] '[] = 'True
  EqC '[] ('(,) q _ ': tl) = EqCAuxZero (IsNullQ q) tl
  EqC ('(,) q _ ': tl) '[] = EqCAuxZero (IsNullQ q) tl
  EqC ('(,) qA sqA ': tlA) ('(,) qB sqB ': tlB) =
    EqCAux (IsNullQ qA) (IsNullQ qB) qA sqA tlA qB sqB tlB

type family EqCAuxZero (b :: Bool) (c :: C) :: Bool where
  EqCAuxZero 'True c = EqC '[] c
  EqCAuxZero 'False _ = 'False

type family EqCAux
  (nullA :: Bool) (nullB :: Bool)
  (qA :: Q) (sqA :: [Z]) (cA :: C)
  (qB :: Q) (sqB :: [Z]) (cB :: C) :: Bool where
    EqCAux 'True 'True _ _ cA _ _ cB = EqC cA cB
    EqCAux 'True 'False _ _ cA qB sqB cB = EqC cA ('(,) qB sqB ': cB)
    EqCAux 'False 'True qA sqA cA _ _ cB = EqC ('(,) qA sqA ': cA) cB
    EqCAux 'False 'False qA sqA cA qB sqB cB =
      And
        (EqQ qA qB)
        (And
          (EqListZ sqA sqB)
          (EqC cA cB)
        )

type family AddC (a :: C) (b :: C) :: C where
  AddC '[] b = b
  AddC a '[] = a
  AddC ('(,) qA sqA ': tlA) ('(,) qB sqB ': tlB) =
    AddCAux (CompareListZ sqA sqB) qA sqA tlA qB sqB tlB

type family AddCAux (ord :: Ordering)
  (qA :: Q) (sqA :: [Z]) (cA :: C)
  (qB :: Q) (sqB :: [Z]) (cB :: C) :: C where
    AddCAux 'LT qA sqA cA qB sqB cB = ('(,) qA sqA ': AddC cA ('(,) qB sqB ': cB))
    AddCAux 'EQ qA sqA cA qB sqB cB = ('(,) (AddQ qA qB) sqA ': AddC cA cB)
    AddCAux 'GT qA sqA cA qB sqB cB = ('(,) qB sqB ': AddC ('(,) qA sqA ': cA) cB)

type family MultC (a :: C) (b :: C) :: C where
  MultC '[] _ = '[]
  MultC _ '[] = '[]
  MultC ('(,) qA sqA ': tlA) ('(,) qB sqB ': tlB) =
    AddC
      (MultMono (MultQ qA qB) sqA sqB)
      (AddC
        (MultC ('(,) qA sqA ': '[]) tlB)
        (AddC
          (MultC tlA ('(,) qB sqB ': '[]))
          (MultC tlA tlB)
        )
      )
type family MultMono (q :: Q) (sqA :: [Z]) (sqB :: [Z]) :: C where
  MultMono q sqA sqB = AuxMultMono q '[] (Reverse sqA) (Reverse sqB)
type family AuxMultMono (q :: Q) (acc :: [Z]) (sqA :: [Z]) (sqB :: [Z]) :: C where
  AuxMultMono q acc '[] sq = ('(,) q (Concat (Reverse sq) acc) ': '[])
  AuxMultMono q acc sq '[] = ('(,) q (Concat (Reverse sq) acc) ': '[])
  AuxMultMono q acc (a ': tlA) (b ': tlB) =
    AuxMultMonoAux (CompareZ a b) q acc a tlA b tlB

type family AuxMultMonoAux (ord :: Ordering)
  (q :: Q) (acc :: [Z])
  (a :: Z) (tlA :: [Z])
  (b :: Z) (tlB :: [Z]) :: C where
    AuxMultMonoAux 'LT q acc a tlA b tlB =
      AuxMultMono q (b ': acc) (a ': tlA) tlB
    AuxMultMonoAux 'EQ q acc a tlA b tlB =
      AuxMultMono (MultQ q (CastZQ a)) acc tlA tlB
    AuxMultMonoAux 'GT q acc a tlA b tlB =
      AuxMultMono q (a ': acc) tlA (b ': tlB)

type family ZeroC :: C where
  ZeroC = '[]

type family OneC :: C where
  OneC = '(,) OneQ '[] ': '[]

type family IC :: C where
  IC = '(,) OneQ ('Int 'Negative OneN ': '[]) ': '[]

type family Sqrt2on2 :: C where
  Sqrt2on2 = '(,) (InvZ (CastNZ TwoN)) (CastNZ TwoN ': '[]) ': '[]

type family Opp (x :: C) :: C where
  Opp '[] = '[]
  Opp ('(,) ('Fraction ('Int s n) den) sq ': tl) =
    '(,) ('Fraction ('Int (Negate s) n) den) sq ': Opp tl

type family InvC (x :: C) :: C where
  InvC ('(,) q sq ': '[]) =
    AuxInv q sq sq
type family AuxInv (q :: Q) (acc :: [Z]) (sq :: [Z]) :: C where
  AuxInv q '[] sq = '(,) q sq ': '[]
  AuxInv q (x ': tl) sq =
    AuxInv (MultQ q (CastZQ x)) tl sq

type family NormalizeC (x :: C) :: C where
  NormalizeC '[] = '[]
  NormalizeC ('(,) q sq ': tl) =
    IfThenElse
      (IsNullQ q)
      (NormalizeC tl)
      ('(,) (Simplify q) sq ': NormalizeC tl)

type family DivC (x :: C) (y :: C) :: C where
  DivC x y = MultC x (InvC y)