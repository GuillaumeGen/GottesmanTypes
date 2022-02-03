{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Nat where

import Data.Kind ( Type )

data Nat = ZN | SN Nat

data IsNat (n :: Nat) :: Type where
  IsZ :: IsNat 'ZN
  IsS :: IsNat n -> IsNat ('SN n)

type family EqN (m :: Nat) (n :: Nat) :: Bool where
  EqN 'ZN 'ZN = 'True
  EqN 'ZN _ = 'False
  EqN _ 'ZN = 'False
  EqN ('SN m) ('SN n) = EqN m n

type family AddN (m :: Nat) (n :: Nat) :: Nat where
  AddN 'ZN n = n
  AddN ('SN m) n = 'SN (AddN m n)

type family MultN (m :: Nat) (n :: Nat) :: Nat where
  MultN 'ZN _ = 'ZN
  MultN ('SN m) n = AddN n (MultN m n)

type family Pred (n :: Nat) :: Nat where
  -- Pred 'ZN = error "Zero has no predecessor"
  Pred ('SN n) = n

type family Twice (n :: Nat) :: Nat where
  Twice 'ZN = 'ZN
  Twice ('SN n) = 'SN ('SN (Twice n))

type family SubN (m :: Nat) (n :: Nat) :: Nat where
  SubN m 'ZN = m
  -- Sub 'ZN ('SN n) = error "Impossible to get a negative natural."
  SubN ('SN m) ('SN n) = SubN m n

type family Geq (m :: Nat) (n :: Nat) :: Bool where
  Geq m 'ZN = 'True
  Geq 'ZN ('SN n) = 'False
  Geq ('SN m) ('SN n) = Geq m n

type family Compare (x :: Nat) (y :: Nat) :: Ordering where
  Compare ('SN _) 'ZN = 'GT
  Compare 'ZN 'ZN = 'EQ
  Compare 'ZN ('SN _) = 'LT
  Compare ('SN x) ('SN y) = Compare x y

type family Odd (n :: Nat) :: Bool where
  Odd 'ZN = 'False
  Odd ('SN n) = Even n

type family Even (n :: Nat) :: Bool where
  Even 'ZN = 'True
  Even ('SN n) = Odd n

type family Quo (m :: Nat) (d :: Nat) :: Nat where
  Quo m d = AuxQuo d m d 'ZN
type family AuxQuo (d :: Nat) (toProc :: Nat) (untilNext :: Nat) (acc :: Nat) :: Nat where
  AuxQuo d toProc 'ZN acc = AuxQuo d toProc d ('SN acc)
  AuxQuo d 'ZN ('SN _) acc = acc
  AuxQuo d ('SN n) ('SN untilNext) acc = AuxQuo d n untilNext acc

type family Rem (m :: Nat) (d :: Nat) :: Nat where
  Rem m d = SubN m (MultN d (Quo m d))

type family PGCD (a :: Nat) (b :: Nat) :: Nat where
  PGCD a 'ZN = a
  PGCD a b = PGCD b (Rem a b)

type family CompareN (x :: Nat) (y :: Nat) :: Ordering where
  CompareN 'ZN 'ZN = 'EQ
  CompareN 'ZN ('SN _) = 'LT
  CompareN ('SN _) 'ZN = 'GT
  CompareN ('SN x) ('SN y) =
    CompareN x y

-- One can count

type family OneN :: Nat where
  OneN = 'SN 'ZN

type family TwoN :: Nat where
  TwoN = 'SN OneN

type family ThreeN :: Nat where
  ThreeN = 'SN TwoN

type family FourN :: Nat where
  FourN = 'SN ThreeN

type family FiveN :: Nat where
  FiveN = 'SN FourN

_0 :: IsNat 'ZN
_0 = IsZ

_1 :: IsNat OneN
_1 = IsS _0

_2 :: IsNat TwoN
_2 = IsS _1

_3 :: IsNat ThreeN
_3 = IsS _2

_4 :: IsNat FourN
_4 = IsS _3

_5 :: IsNat FiveN
_5 = IsS _4
