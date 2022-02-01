{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module List where

import Data.Kind ( Type )

import Nat

data IsList (f :: a -> Type) (l :: [a]) :: Type where
  IsN :: IsList f '[]
  IsC :: f x -> IsList f l -> IsList f (x ': l)

-- Two useful functions

type family Length (l :: [a]) :: Nat where
  Length '[] = 'ZN
  Length (x ': tl) = 'SN (Length tl)

type family Get (l :: [a]) (n :: Nat) :: a where
  Get (x ': tl) 'ZN = x
  Get (x ': tl) ('SN n) = Get tl n

type family Reverse (l :: [a]) :: [a] where
  Reverse l = AuxReverse '[] l
type family AuxReverse (acc :: [a]) (l :: [a]) :: [a] where
  AuxReverse acc '[] = acc
  AuxReverse acc (x ': tl) = AuxReverse (x ': acc) tl

type family Concat (lA :: [a]) (lB :: [a]) :: [a] where
  Concat '[] lB = lB
  Concat (x ': tlA) lB = x ': Concat tlA lB
