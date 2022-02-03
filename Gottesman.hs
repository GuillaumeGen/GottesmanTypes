{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Gottesman where

import Data.Kind ( Type )

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

type family TheMat (x :: BasicBrick) :: Type where
  TheMat x = IsMatC (MatOf x)

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

superdenseCoding :: GottesmanType ('I ': 'I ': 'Z ': 'I ': '[])
                 -> GottesmanType ('Z ': 'I ': 'Z ': 'I ': '[])
superdenseCoding (q1, (q2, (q3, (q4, c)))) =
  let (q3', c1) = on H_ q3 in
  let (q3'', q4', c2) = onControlled X_ q3' q4 in
  let (q1', q3''', c3) = onControlled Z_ q1 q3'' in
  let (q2', q3'''', c4) = onControlled X_ q2 q3''' in
  let (q3''''', q4'', c5) = onControlled X_ q3'''' q4' in
  let (q3'''''', c6) = on H_ q3''''' in
  (q1', (q2', (q3'''''', (q4'', multIsC c (multIsC c1 (multIsC c2 (multIsC c3 (multIsC c4 (multIsC c5 c6)))))))))

-- * Now we have to apply transformation on a specific qubit, given a family.

type family GottesmanType (l :: [BasicBrick]) :: * where
  GottesmanType l = AuxGottesmanType OneC l
type family AuxGottesmanType (acc :: C) (l :: [BasicBrick]) :: * where
  AuxGottesmanType c '[] = IsC (NormalizeC c)
  AuxGottesmanType c (hd ': tl) = SecondAuxGottesmanType c tl (OneHeaded (MatOf hd))
type family SecondAuxGottesmanType (acc :: C) (l :: [BasicBrick]) (p :: (Mat C, C)) :: * where
  SecondAuxGottesmanType c l ('(,) m d) = (IsMatC m, AuxGottesmanType (MultC c d) l)

on :: IsBasicBrick x -> IsMatC m -> OneHeadedType (Conjugate m x)
on = undefined

onControlled :: IsBasicBrick x -> IsMatC controller -> IsMatC m
             -> UnsafeUntensor44Type (MatrixControl (MatOf x) × (controller ⊗ m) × MatrixControl (InvOf x))
onControlled = undefined
