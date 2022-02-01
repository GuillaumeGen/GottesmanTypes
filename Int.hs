{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Int where

import Data.Kind ( Type )

import Bool
import Nat

-- A type to represent the sign of integers

data Sign = Positive | Negative

data IsSign (s :: Sign) :: Type where
  IsPos :: IsSign 'Positive
  IsNeg :: IsSign 'Negative

type family EqSign (s1 :: Sign) (s2 :: Sign) :: Bool where
  EqSign 'Positive 'Positive = 'True
  EqSign 'Negative 'Negative = 'True
  EqSign _ _ = 'False

type family Negate (s :: Sign) :: Sign where
  Negate 'Positive = 'Negative
  Negate 'Negative = 'Positive

-- The type of integers

data Z =
  Int {
    sign :: Sign,
    valAbs :: Nat
  }

data IsZ (i :: Z) :: Type where
  IsI :: IsSign s -> IsNat n -> IsZ ('Int s n)

type family EqZ (a :: Z) (b :: Z) :: Bool where
  EqZ ('Int _ 'ZN) ('Int _ 'ZN) = 'True
  EqZ ('Int sA nA) ('Int sB nB) =
    And (EqSign sA sB) (EqN nA nB)

type family ZeroZ :: Z where
  ZeroZ = CastNZ 'ZN

type family CastNZ (n :: Nat) :: Z where
  CastNZ n = 'Int 'Positive n

type family AddZ (m :: Z) (n :: Z) :: Z where
  AddZ ('Int 'Positive m) ('Int 'Positive n) =
    'Int 'Positive (AddN m n)
  AddZ ('Int 'Positive m) ('Int 'Negative n) =
    IfThenElse
      (Geq m n)
      ('Int 'Positive (SubN m n))
      ('Int 'Negative (SubN n m))
  AddZ ('Int 'Negative m) ('Int 'Positive n) =
    IfThenElse
      (Geq n m)
      ('Int 'Positive (SubN n m))
      ('Int 'Negative (SubN m n))
  AddZ ('Int 'Negative m) ('Int 'Negative n) =
    'Int 'Negative (AddN m n)

type family MultZ (m :: Z) (n :: Z) :: Z where
  MultZ ('Int _ 'ZN) _ = ZeroZ
  MultZ _ ('Int _ 'ZN) = ZeroZ
  MultZ ('Int 'Positive m) ('Int 'Positive n) =
    'Int 'Positive (MultN m n)
  MultZ ('Int 'Positive m) ('Int 'Negative n) =
    'Int 'Negative (MultN m n)
  MultZ ('Int 'Negative m) ('Int 'Positive n) =
    'Int 'Negative (MultN m n)
  MultZ ('Int 'Negative m) ('Int 'Negative n) =
    'Int 'Positive (MultN m n)

type family EqListZ (lA :: [Z]) (lB :: [Z]) :: Bool where
  EqListZ '[] '[] = 'True
  EqListZ '[] _ = 'False
  EqListZ _ '[] = 'False
  EqListZ (a ': tlA) (b ': tlB) =
    And
      (EqZ a b)
      (EqListZ tlA tlB)

type family CompareZ (x :: Z) (y :: Z) (smX :: a) (eq :: a) (smY :: a) :: a where
  CompareZ ('Int 'Negative x) ('Int 'Negative y) smX eq smY =
    CompareN x y smY eq smX
  CompareZ ('Int 'Negative x) ('Int 'Positive y) smX _ _ = smX
  CompareZ ('Int 'Positive x) ('Int 'Negative y) _ _ smY = smY
  CompareZ ('Int 'Positive x) ('Int 'Positive y) smX eq smY =
    CompareN x y smX eq smY

type family CompareListZ (x :: [Z]) (y :: [Z]) (smX :: a) (eq :: a) (smY :: a) :: a where
  CompareListZ '[] '[] _ eq _ = eq
  CompareListZ (_ ': _) '[] _ _ smY = smY
  CompareListZ '[] (_ ': _) smX _ _ = smX
  CompareListZ (x ': tlX) (y ': tlY) smX eq smY =
    CompareZ x y
      smX
      (CompareListZ tlX tlY smX eq smY)
      smY

type family OneZ :: Z where
  OneZ = CastNZ OneN