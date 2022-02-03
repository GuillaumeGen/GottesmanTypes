{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Pair where

import Data.Kind ( Type )

data IsPair (f :: a -> Type) (g :: b -> Type) (l :: (a, b)) :: Type where
  IsPair :: f a -> g b -> IsPair f g ('(,) a b)
  