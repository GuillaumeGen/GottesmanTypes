{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Bool where

import Data.Kind ( Type )

data IsBool (b :: Bool) :: Type where
  IsT :: IsBool 'True
  IsF :: IsBool 'False

type family EqB (a :: Bool) (b :: Bool) :: Bool where
  EqB 'True 'True = 'True
  EqB 'False 'False = 'True
  EqB _ _ = 'False

type family Neg (b :: Bool) :: Bool where
  Neg 'True = 'False
  Neg 'False = 'True

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True b = b
  And 'False _ = 'False

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or 'True _ = 'True
  Or 'False b = b

type family IfThenElse (b :: Bool) (x :: a) (y :: a) :: a where
  IfThenElse 'True x _ = x
  IfThenElse 'False _ y = y

type family IfThenFail (b :: Bool) (x :: a) :: a where
  IfThenFail 'True x = x
  -- IfThenFail 'False _ = error "The check failed"
