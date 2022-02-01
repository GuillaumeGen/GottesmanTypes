{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Gottesman where

import Data.Kind ( Type )

import Bool
import Nat
import Int
import Rational
import Complex
import Matrix

-- * The six fundamental matrices

data BasicBrick = X | Y | Z | I | H | S

data IsBasicBrick (x :: BasicBrick) :: Type where
  X_ :: IsBasicBrick 'X
  Y_ :: IsBasicBrick 'Y
  Z_ :: IsBasicBrick 'Z
  I_ :: IsBasicBrick 'I
  H_ :: IsBasicBrick 'H
  S_ :: IsBasicBrick 'S

type family MatOf (x :: BasicBrick) :: Mat C where
  MatOf 'X =
    'Mat ((ZeroC ': OneC ': '[]) ': (OneC ': ZeroC ': '[]) ': '[])
  MatOf 'Y =
    'Mat ((ZeroC ': Opp IC ': '[]) ': (IC ': ZeroC ': '[]) ': '[])
  MatOf ' Z =
    'Mat ((OneC ': ZeroC ': '[]) ': (ZeroC ': Opp OneC ': '[]) ': '[])
  MatOf 'I =
    'Mat ((OneC ': ZeroC ': '[]) ': (ZeroC ': OneC ': '[]) ': '[])
  MatOf 'H =
    'Mat ((Sqrt2on2 ': Sqrt2on2 ': '[]) ': (Sqrt2on2 ': Opp Sqrt2on2 ': '[]) ': '[])
  MatOf 'S =
    'Mat ((OneC ': ZeroC ': '[]) ': (ZeroC ': IC ': '[]) ': '[])

type family InvOf (x :: BasicBrick) :: Mat C where
  InvOf 'X = MatOf 'X
  InvOf 'Y = MatOf 'Y
  InvOf 'Z = MatOf 'Z
  InvOf 'I = MatOf 'I
  InvOf 'H = MatOf 'H
  InvOf 'S =
    'Mat ((OneC ': ZeroC ': '[]) ': (ZeroC ': Opp IC ': '[]) ': '[])

type family Conjugate (m :: Mat C) (x :: BasicBrick) :: Mat C where
  Conjugate m x = MatOf x × m × InvOf x

type family IsMatC (m :: Mat C) :: Type where
  IsMatC m = IsMat IsC m

type family TheMat (x :: BasicBrick) :: Type where
  TheMat x = IsMatC(MatOf x)

-- A safe version is provided, which checks that the result is valid.
-- TODO: It requires EqMat, which required EqC

-- type family SafeUntensor44 (m :: Mat C) :: (Mat C, Mat C) where
--   SafeUntensor44 m = AuxSafeUntensor m (UnsafeUntensor44 m)
-- type family AuxSafeUntensor (m :: Mat C) (res :: (Mat C, Mat C)) :: (Mat C, Mat C) where
--   AuxSafeUntensor m ('(,) a b) = IfThenFail (EqMat m (a ⊗ b)) ('(,) a b)

-- * A few tests already verifying types of I, H and S presented in the paper.

wire :: IsMatC m -> IsMatC (NormalizeMatC (Conjugate m 'I))
wire = undefined

h :: IsMatC m -> IsMatC (NormalizeMatC (Conjugate m 'H))
h = undefined

s :: IsMatC m -> IsMatC (NormalizeMatC (Conjugate m 'S))
s = undefined

testWire :: TheMat 'X -> TheMat 'X
testWire = wire

testH1 :: TheMat 'X -> TheMat 'Z
testH1 = h

testH2 :: TheMat 'Z -> TheMat 'X
testH2 = h

testS1 :: TheMat 'X -> TheMat 'Y
testS1 = s

testS2 :: TheMat 'Z -> TheMat 'Z
testS2 = s

-- The main transformation of section 5 of the article on Gottesman types
-- But to avoid killing GHC, one wire is removed in each transformation (first or last depending on which one is touched).

-- step1 :: IsMatC (MatOf 'I ⊗ MatOf 'Z ⊗ MatOf 'I) -> IsMatC (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I)
-- step1 = on H_ _1 _3

step2 :: IsMatC (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I) -> IsMatC (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'X)
step2 = onControlled X_ _1 _2 _3

-- step3 :: IsMatC (MatOf 'I ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMatC (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X)
-- step3 = onControlled Z_ _0 _2 _3

-- step4 :: IsMatC (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMatC (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X)
-- step4 = onControlled X_ _1 _2 _3

-- step5 :: IsMatC (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'X) -> IsMatC (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I)
-- step5 = onControlled X_ _1 _2 _3

-- step6 :: IsMatC (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMatC (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'Z)
-- step6 = on H_ _2 _3

-- * Now we have to apply transformation on a specific qubit, given a family.

-- We assume that the qubits are 0-indexed
type family OnAmong (x :: BasicBrick) (n :: Nat) (size :: Nat) (m :: Mat C) :: Mat C where
  OnAmong x n size m = OnMat (MatOf x) (InvOf x) n size m

type family OnMat (left :: Mat C) (right :: Mat C) (n :: Nat) (size :: Nat) (m :: Mat C) :: Mat C where
  OnMat left right n size m =
    ConjugateWith (TensorIRight (SubN size n) (TensorILeft n ('(,) left right))) m

on :: IsBasicBrick x -> IsNat n -> IsNat size -> IsMatC m -> IsMatC (NormalizeMatC (OnAmong x n size m))
on = undefined

onControlled :: IsBasicBrick x -> IsNat controller -> IsNat n -> IsNat size -> IsMatC m -> IsMatC (NormalizeMatC (OnControl x controller n size m))
onControlled = undefined

type family OnControl (x :: BasicBrick) (controller :: Nat) (n :: Nat) (size :: Nat) (m :: Mat C) :: Mat C where
  OnControl x controller n size m = OnControlGuarded x controller n size m (Geq controller n)
type family OnControlGuarded (x :: BasicBrick) (controller :: Nat) (n :: Nat) (size :: Nat) (m :: Mat C) (b :: Bool) :: Mat C where
  OnControlGuarded x controller n size m 'True = OnControlRight (MatOf x) (InvOf x) controller n size (SubN controller n) m
  OnControlGuarded x controller n size m 'False = OnControlLeft (MatOf x) (InvOf x) controller n size (SubN n controller) m

type family OnControlRight (left :: Mat C) (right :: Mat C) (controller :: Nat) (n :: Nat) (size :: Nat) (diff :: Nat) (m :: Mat C) :: Mat C where
  OnControlRight left right controller n size diff m =
    ConjugateWith (TensorIRight (SubN size controller) (TensorILeft n (ControlledRightDiff left right diff))) m

type family OnControlLeft (left :: Mat C) (right :: Mat C) (controller :: Nat) (n :: Nat) (size :: Nat) (diff :: Nat) (m :: Mat C) :: Mat C where
  OnControlLeft left right controller n size diff m =
    ConjugateWith (TensorIRight (SubN size n) (TensorILeft controller (ControlledLeftDiff left right diff))) m

type family ControlledRightDiff (left :: Mat C) (right :: Mat C) (diff :: Nat) :: (Mat C, Mat C) where
  ControlledRightDiff l r ('SN 'ZN) = '(,) (MatrixCRight l) (MatrixCRight r)
  ControlledRightDiff l r ('SN n) =
    ControlledRightDiff (l ⊗ MatOf 'I) (r ⊗ InvOf 'I) n

type family ControlledLeftDiff (left :: Mat C) (right :: Mat C) (diff :: Nat) :: (Mat C, Mat C) where
  ControlledLeftDiff l r ('SN 'ZN) = '(,) (MatrixCLeft l) (MatrixCLeft r)
  ControlledLeftDiff l r ('SN n) =
    ControlledLeftDiff (MatOf 'I ⊗ l) (InvOf 'I ⊗ r) n

type family MatrixCRight (m :: Mat C) :: Mat C where
  MatrixCRight m = FillMatrix (Interleaved m) (Twice (NbLines m)) (Twice (NbCols m))

type family MatrixCLeft (m :: Mat C) :: Mat C where
  MatrixCLeft m = FillMatrix (DiagIM m) (Twice (NbLines m)) (Twice (NbCols m))

type family TensorIRight (n :: Nat) (m :: (Mat C, Mat C)) :: (Mat C, Mat C) where
  TensorIRight ('SN 'ZN) m = m
  TensorIRight ('SN ('SN n)) ('(,) left right) = TensorIRight ('SN n) ('(,) (left ⊗ MatOf 'I) (right ⊗ InvOf 'I))

type family TensorILeft (n :: Nat) (m :: (Mat C, Mat C)) :: (Mat C, Mat C) where
  TensorILeft 'ZN m = m
  TensorILeft ('SN n) ('(,) left right) = TensorILeft n ('(,) (MatOf 'I ⊗ left) (InvOf 'I ⊗ right))

type family ConjugateWith (x :: (Mat C, Mat C)) (m :: Mat C) :: Mat C where
  ConjugateWith ('(,) left right) m = left × m × right
