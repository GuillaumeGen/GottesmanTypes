{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Rational where

import Data.Kind ( Type )

import Bool
import Nat
import Int

data Q =
  Fraction {
    numerator :: Z,
    denominator :: Nat
  }

data IsQ (i :: Q) :: Type where
  IsFrac :: IsZ m -> IsNat n -> IsQ ('Fraction m n)

type family ZeroQ :: Q where
  ZeroQ = 'Fraction ZeroZ OneN

type family IsNullQ (m :: Q) :: Bool where
  IsNullQ ('Fraction ('Int _ 'ZN) _) = 'True
  IsNullQ _ = 'False

type family Simplify (m ::Q) :: Q where
  Simplify ('Fraction ('Int _ 'ZN) ('SN d)) = ZeroQ
  Simplify ('Fraction ('Int s num) ('SN d)) = AuxFrac s num ('SN d) (PGCD num ('SN d))
type family AuxFrac (s :: Sign) (num :: Nat) (d :: Nat) (pgcd :: Nat) :: Q where
  AuxFrac s num d pgcd = 'Fraction ('Int s (Quo num pgcd)) (Quo d pgcd)

type family EqQ (a :: Q) (b :: Q) :: Bool where
  EqQ ('Fraction ('Int _ 'ZN) _) ('Fraction ('Int _ 'ZN) _) = 'True
  EqQ ('Fraction ('Int sA numA) denA) ('Fraction ('Int sB numB) denB) =
    And (EqSign sA sB) (EqN (MultN numA denB) (MultN numB denA))

type family AddQ (a :: Q) (b :: Q) :: Q where
  AddQ ('Fraction numA denA) ('Fraction numB denB) =
    'Fraction
      (AddZ (MultZ numA (CastNZ denB)) (MultZ numB (CastNZ denA)))
      (MultN denA denB)

type family MultQ (a :: Q) (b :: Q) :: Q where
  MultQ ('Fraction ('Int _ 'ZN) _) _ = ZeroQ
  MultQ _ ('Fraction ('Int _ 'ZN) _) = ZeroQ
  MultQ ('Fraction numA denA) ('Fraction numB denB) =
    'Fraction
      (MultZ numA numB)
      (MultN denA denB)

type family InvZ (n :: Z) :: Q where
  InvZ ('Int s n) = 'Fraction ('Int s ('SN 'ZN)) n

type family CastZQ (z :: Z) :: Q where
  CastZQ z = 'Fraction z ('SN 'ZN)

type family OneQ :: Q where
  OneQ = CastZQ OneZ
