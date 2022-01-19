{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Gottesman where

import Data.Kind ( Type )

-- * The six fundamental matrices

data BasicBrick = X | Y | Z | I | H | S

data IsBasicBrick (x :: BasicBrick) :: Type where
  X_ :: IsBasicBrick 'X
  Y_ :: IsBasicBrick 'Y
  Z_ :: IsBasicBrick 'Z
  I_ :: IsBasicBrick 'I
  H_ :: IsBasicBrick 'H
  S_ :: IsBasicBrick 'S

type family MatOf (x :: BasicBrick) :: Mat Complex where
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

type family InvOf (x :: BasicBrick) :: Mat Complex where
  InvOf 'X = MatOf 'X
  InvOf 'Y = MatOf 'Y
  InvOf 'Z = MatOf 'Z
  InvOf 'I = MatOf 'I
  InvOf 'H = MatOf 'H
  InvOf 'S =
    'Mat ((OneC ': ZeroC ': '[]) ': (ZeroC ': Opp IC ': '[]) ': '[])

type family Conjugate (m :: Mat Complex) (x :: BasicBrick) :: Mat Complex where
  Conjugate m x = MatOf x × m × InvOf x

type family TheMat (x :: BasicBrick) :: Type where
  TheMat x = IsMat (MatOf x)

-- * A few tests already verifying types of I, H and S presented in the paper.

wire :: IsMat m -> IsMat (Conjugate m 'I)
wire = undefined

h :: IsMat m -> IsMat (Conjugate m 'H)
h = undefined

s :: IsMat m -> IsMat (Conjugate m 'S)
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

step1 :: IsMat (MatOf 'I ⊗ MatOf 'Z ⊗ MatOf 'I) -> IsMat (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I)
step1 = on H_ _1 _3

step2 :: IsMat (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I) -> IsMat (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'X)
step2 = onControlled X_ _1 _2 _3

step3 :: IsMat (MatOf 'I ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMat (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X)
step3 = onControlled Z_ _0 _2 _3

step4 :: IsMat (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMat (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X)
step4 = onControlled X_ _1 _2 _3

step5 :: IsMat (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'X) -> IsMat (MatOf 'I ⊗ MatOf 'X ⊗ MatOf 'I)
step5 = onControlled X_ _1 _2 _3

step6 :: IsMat (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'X) -> IsMat (MatOf 'Z ⊗ MatOf 'I ⊗ MatOf 'Z)
step6 = on H_ _2 _3

-- * Now we have to apply transformation on a specific qubit, given a family.

-- We assume that the qubits are 0-indexed
type family OnAmong (x :: BasicBrick) (n :: Nat) (size :: Nat) (m :: Mat Complex) :: Mat Complex where
  OnAmong x n size m = OnMat (MatOf x) (InvOf x) n size m

type family OnMat (left :: Mat Complex) (right :: Mat Complex) (n :: Nat) (size :: Nat) (m :: Mat Complex) :: Mat Complex where
  OnMat left right n size m =
    ConjugateWith (TensorIRight (Sub size n) (TensorILeft n ('(,) left right))) m

on :: IsBasicBrick x -> IsNat n -> IsNat size -> IsMat m -> IsMat (OnAmong x n size m)
on = undefined

onControlled :: IsBasicBrick x -> IsNat controller -> IsNat n -> IsNat size -> IsMat m -> IsMat (OnControl x controller n size m)
onControlled = undefined

type family OnControl (x :: BasicBrick) (controller :: Nat) (n :: Nat) (size :: Nat) (m :: Mat Complex) :: Mat Complex where
  OnControl x controller n size m = OnControlGuarded x controller n size m (Geq controller n)
type family OnControlGuarded (x :: BasicBrick) (controller :: Nat) (n :: Nat) (size :: Nat) (m :: Mat Complex) (b :: Bool) :: Mat Complex where
  OnControlGuarded x controller n size m 'True = OnControlRight (MatOf x) (InvOf x) controller n size (Sub controller n) m
  OnControlGuarded x controller n size m 'False = OnControlLeft (MatOf x) (InvOf x) controller n size (Sub n controller) m

type family OnControlRight (left :: Mat Complex) (right :: Mat Complex) (controller :: Nat) (n :: Nat) (size :: Nat) (diff :: Nat) (m :: Mat Complex) :: Mat Complex where
  OnControlRight left right controller n size diff m =
    ConjugateWith (TensorIRight (Sub size controller) (TensorILeft n (ControlledRightDiff left right diff))) m

type family OnControlLeft (left :: Mat Complex) (right :: Mat Complex) (controller :: Nat) (n :: Nat) (size :: Nat) (diff :: Nat) (m :: Mat Complex) :: Mat Complex where
  OnControlLeft left right controller n size diff m =
    ConjugateWith (TensorIRight (Sub size n) (TensorILeft controller (ControlledLeftDiff left right diff))) m

type family ControlledRightDiff (left :: Mat Complex) (right :: Mat Complex) (diff :: Nat) :: (Mat Complex, Mat Complex) where
  ControlledRightDiff l r ('SN 'ZN) = '(,) (MatrixCRight l) (MatrixCRight r)
  ControlledRightDiff l r ('SN n) =
    ControlledRightDiff (l ⊗ MatOf 'I) (r ⊗ InvOf 'I) n

type family ControlledLeftDiff (left :: Mat Complex) (right :: Mat Complex) (diff :: Nat) :: (Mat Complex, Mat Complex) where
  ControlledLeftDiff l r ('SN 'ZN) = '(,) (MatrixCLeft l) (MatrixCLeft r)
  ControlledLeftDiff l r ('SN n) =
    ControlledLeftDiff (MatOf 'I ⊗ l) (InvOf 'I ⊗ r) n

type family MatrixCRight (m :: Mat Complex) :: Mat Complex where
  MatrixCRight m = FillMatrix (Interleaved m) (Twice (NbLines m)) (Twice (NbCols m))

type family MatrixCLeft (m :: Mat Complex) :: Mat Complex where
  MatrixCLeft m = FillMatrix (DiagIM m) (Twice (NbLines m)) (Twice (NbCols m))

type family TensorIRight (n :: Nat) (m :: (Mat Complex, Mat Complex)) :: (Mat Complex, Mat Complex) where
  TensorIRight ('SN 'ZN) m = m
  TensorIRight ('SN ('SN n)) ('(,) left right) = TensorIRight ('SN n) ('(,) (left ⊗ MatOf 'I) (right ⊗ InvOf 'I))

type family TensorILeft (n :: Nat) (m :: (Mat Complex, Mat Complex)) :: (Mat Complex, Mat Complex) where
  TensorILeft 'ZN m = m
  TensorILeft ('SN n) ('(,) left right) = TensorILeft n ('(,) (MatOf 'I ⊗ left) (InvOf 'I ⊗ right))

type family ConjugateWith (x :: (Mat Complex, Mat Complex)) (m :: Mat Complex) :: Mat Complex where
  ConjugateWith ('(,) left right) m = left × m × right

-- * Matrices related functions

data Mat (a :: Type) :: Type where
  Mat :: [[a]] -> Mat a

data IsMat (m :: Mat Complex) :: Type where
  IsM :: IsListL l -> IsMat ('Mat l)

type family NbLines (m :: Mat a) :: Nat where
  NbLines ('Mat l) = Length l

type family NbCols (m :: Mat a) :: Nat where
  NbCols ('Mat (l ': _)) = Length l

type family Access (m :: Mat a) (l :: Nat) (c :: Nat) :: a where
  Access ('Mat lines) l c = Get (Get lines l) c

type family (×) (a :: Mat Complex) (b :: Mat Complex) :: Mat Complex where
  a × b = FillMatrix (PartialOneProd a b) (NbLines a) (NbCols b)

type family (⊗) (a :: Mat Complex) (b :: Mat Complex) :: Mat Complex where
  a ⊗ b = FillMatrix (PartialOneTens a b) (MultN (NbLines a) (NbLines b)) (MultN (NbCols a) (NbCols b))

-- Here the f is of type * and not Nat -> Nat -> a because of the defunctionalisation required to partially applied type families.
type family FillMatrix (f :: *) (lMax :: Nat) (cMax :: Nat) :: Mat a where
  FillMatrix f lMax cMax = AuxFillMatrix f cMax lMax cMax '[] '[]
type family AuxFillMatrix
  (f :: *)
  (cMax :: Nat)
  (lIndex :: Nat)
  (cIndex :: Nat)
  (accMat :: [[a]])
  (accLine :: [a]) :: Mat a where
    AuxFillMatrix _ _ 'ZN _ m _ = 'Mat m
    AuxFillMatrix f cMax ('SN l) 'ZN '[] ('Complex n sq h i m ': lTl) =
      AuxFillMatrix f cMax l cMax (('Complex n sq h i m ': lTl) ': '[]) '[]
    AuxFillMatrix f cMax ('SN l) 'ZN (mHd ': mTl) ('Complex n sq h i m ': lTl) =
      AuxFillMatrix f cMax l cMax (('Complex n sq h i m ': lTl) ': mHd ': mTl) '[]
    AuxFillMatrix f cMax ('SN l) ('SN c) mAcc '[] =
      AuxFillMatrix f cMax ('SN l) c mAcc (Apply2 f l c ': '[])
    AuxFillMatrix f cMax ('SN l) ('SN c) mAcc ('Complex n sq h i m ': lTl) =
      AuxFillMatrix f cMax ('SN l) c mAcc (Apply2 f l c ': 'Complex n sq h i m ': lTl)

data Interleaved :: Mat Complex -> *
data DiagIM :: Mat Complex -> *
data PartialOneProd :: Mat Complex -> Mat Complex -> *
type family Apply2 (f :: *) (x :: k1) (y :: k2) :: k3 where
  Apply2 (PartialOneProd m1 m2) l c = AuxComputeOneProd m1 m2 (NbLines m2) l c 'ZN ZeroC (EqN 'ZN (NbLines m2))
  Apply2 (PartialOneTens m1 m2) l c = AuxComputeOneTens m1 m2 (Quo l (NbLines m2)) (Rem l (NbLines m2)) (Quo c (NbCols m2)) (Rem c (NbCols m2))
  Apply2 (Interleaved m) l c = AuxInterleaved m l c (Even l) (Even c)
  Apply2 (DiagIM m) l c = AuxDiagIM m l c (Geq l (NbLines m)) (Geq c (NbCols m))

type family AuxInterleaved (m :: Mat Complex) (l :: Nat) (c :: Nat) (evenL :: Bool) (evenC :: Bool) :: Complex where
  AuxInterleaved m l c 'True _ = IfThenElse (EqN l c) OneC ZeroC
  AuxInterleaved m l c 'False 'True = ZeroC
  AuxInterleaved m l c 'False 'False = Access m (Half (Pred l)) (Half (Pred c))

type family AuxDiagIM (m :: Mat Complex) (l :: Nat) (c :: Nat) (bigL :: Bool) (bigC :: Bool) :: Complex where
  AuxDiagIM m l c 'True 'True = Access m (Sub l (NbLines m)) (Sub c (NbCols m))
  AuxDiagIM m l c 'True 'False = ZeroC
  AuxDiagIM m l c 'False 'True = ZeroC
  AuxDiagIM m l c 'False 'False = IfThenElse (EqN l c) OneC ZeroC

type family AuxComputeOneProd
  (m1 :: Mat Complex)
  (m2 :: Mat Complex)
  (maxK :: Nat)
  (l :: Nat)
  (c :: Nat)
  (k :: Nat)
  (acc :: Complex)
  (termin :: Bool) :: Complex where
    AuxComputeOneProd m1 m2 maxK l c k ('Complex n sq h i min) 'True = 'Complex n sq h i min
    AuxComputeOneProd m1 m2 maxK l c k ('Complex n sq h i min) 'False =
      AuxComputeOneProd m1 m2 maxK l c ('SN k) ('Complex n sq h i min :+: MultC (Access m1 l k) (Access m2 k c)) (EqN maxK ('SN k))

data PartialOneTens :: Mat Complex -> Mat Complex -> *
type family AuxComputeOneTens
  (m1 :: Mat Complex)
  (m2 :: Mat Complex)
  (qL :: Nat)
  (rL :: Nat)
  (qC :: Nat)
  (rC :: Nat) :: Complex where
    AuxComputeOneTens m1 m2 qL rL qC rC =
      MultC (Access m1 qL qC) (Access m2 rL rC)

-- * Boolean related functions

data IsBool (b :: Bool) :: Type where
  IsT :: IsBool 'True
  IsF :: IsBool 'False

type family Neg (b :: Bool) :: Bool where
  Neg 'True = 'False
  Neg 'False = 'True

type family NEq (a :: Bool) (b :: Bool) :: Bool where
  NEq 'True 'True = 'False
  NEq 'True 'False = 'True
  NEq 'False 'True = 'True
  NEq 'False 'False = 'False

type family IfThenElse (b :: Bool) (x :: a) (y :: a) :: a where
  IfThenElse 'True x _ = x
  IfThenElse 'False _ y = y

-- * Natural number related functions

data Nat = ZN | SN Nat

data IsNat (n :: Nat) :: Type where
  IsZ :: IsNat 'ZN
  IsS :: IsNat n -> IsNat ('SN n)

_0 :: IsNat 'ZN
_0 = IsZ
_1 = IsS _0
_2 = IsS _1
_3 = IsS _2
_4 = IsS _3
_5 = IsS _4

type family Pred (n :: Nat) :: Nat where
  -- Pred 'ZN = error "Zero has no predecessor"
  Pred ('SN n) = n

type family Half (n :: Nat) :: Nat where
  Half 'ZN = 'ZN
  Half ('SN ('SN n)) = 'SN (Half n)
  -- Half ('SN 'ZN) = error "Impossible to divide an odd number by 2"

type family Twice (n :: Nat) :: Nat where
  Twice 'ZN = 'ZN
  Twice ('SN n) = 'SN ('SN (Twice n))

type family Add (m :: Nat) (n :: Nat) :: Nat where
  Add 'ZN n = n
  Add ('SN m) n = 'SN (Add m n)

type family Sub (m :: Nat) (n :: Nat) :: Nat where
  Sub m 'ZN = m
  -- Sub 'ZN ('SN n) = error "Impossible to get a negative natural."
  Sub ('SN m) ('SN n) = Sub m n

type family EqN (m :: Nat) (n :: Nat) :: Bool where
  EqN 'ZN 'ZN = 'True
  EqN 'ZN ('SN _) = 'False
  EqN ('SN _) 'ZN = 'False
  EqN ('SN m) ('SN n) = EqN m n

type family Geq (m :: Nat) (n :: Nat) :: Bool where
  Geq m 'ZN = 'True
  Geq 'ZN ('SN n) = 'False
  Geq ('SN m) ('SN n) = Geq m n

type family Compare (x :: Nat) (y :: Nat) (xBigger :: a) (eq :: a) (xSmaller :: a) :: a where
  Compare ('SN _) 'ZN xBigger _ _ = xBigger
  Compare 'ZN 'ZN _ eq _ = eq
  Compare 'ZN ('SN _) _ _ xSmaller = xSmaller
  Compare ('SN x) ('SN y) xBigger eq xSmaller = Compare x y xBigger eq xSmaller

type family MultN (m :: Nat) (n :: Nat) :: Nat where
  MultN 'ZN _ = 'ZN
  MultN ('SN m) n = Add n (MultN m n)

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
  Rem m d = Sub m (MultN d (Quo m d))

-- * Complex numbers related functions

-- This is a silly representation of "complex numbers",
-- it is just a natural number and 4 modifiers to potentially multiply it by
-- sqrt(2), i, (1/2) and (-1)
data Complex = Complex Nat Bool Bool Bool Bool

data IsComplex (c :: Complex) :: Type where
  IsZCom :: IsNat n -> IsBool sq -> IsBool i -> IsBool h -> IsBool m -> IsComplex ('Complex n sq i h m)

type family ZeroC :: Complex where
  ZeroC = 'Complex 'ZN 'False 'False 'False 'False

type family OneC :: Complex where
  OneC = 'Complex ('SN 'ZN) 'False 'False 'False 'False

type family IC :: Complex where
  IC = 'Complex ('SN 'ZN) 'False 'True 'False 'False

type family Sqrt2on2 :: Complex where
  Sqrt2on2 = 'Complex ('SN 'ZN) 'True 'False 'True 'False

type family Opp (c :: Complex) :: Complex where
  Opp ('Complex a sq i h m) = 'Complex a sq i h (Neg m)

type family (:+:) (a :: Complex) (b :: Complex) :: Complex where
  ('Complex 'ZN _ _ _ _) :+: b = b
  a :+: ('Complex 'ZN _ _ _ _) = a
  ('Complex x sq i 'True 'True) :+: ('Complex y _ _ 'True 'True) =
    'Complex (Half (Add x y)) sq i 'False 'True
  ('Complex x sq i 'True 'True) :+: ('Complex y _ _ 'True 'False) =
    Compare x y
      ('Complex (Half (Sub x y)) sq i 'False 'True)
      ZeroC
      ('Complex (Half (Sub y x)) sq i 'False 'False)
  ('Complex x sq i 'True 'True) :+: ('Complex y _ _ 'False 'True) =
    'Complex (Add x (Twice y)) sq i 'False 'True
  ('Complex x sq i 'True 'True) :+: ('Complex y _ _ 'False 'False) =
    Compare x (Twice y)
      ('Complex (Sub x (Twice y)) sq i 'True 'True)
      ZeroC
      ('Complex (Sub (Twice y) x) sq i 'True 'False)
  ('Complex x sq i 'True 'False) :+: ('Complex y _ _ 'True 'True) =
    Compare x y
      ('Complex (Half (Sub x y)) sq i 'False 'False)
      ZeroC
      ('Complex (Half (Sub y x)) sq i 'False 'True)
  ('Complex x sq i 'True 'False) :+: ('Complex y _ _ 'True 'False) =
    'Complex (Half (Add x y)) sq i 'False 'False
  ('Complex x sq i 'True 'False) :+: ('Complex y sq i 'False 'True) =
    Compare x (Twice y)
      ('Complex (Sub x (Twice y)) sq i 'True 'False)
      ZeroC
      ('Complex (Sub (Twice y) x) sq i 'True 'True)
  ('Complex x sq i 'False 'True) :+: ('Complex y _ _ 'True 'True) =
    'Complex (Add (Twice x) y) sq i 'True 'True
  ('Complex x sq i 'False 'True) :+: ('Complex y sq i 'True 'False) =
    Compare (Twice x) y
      ('Complex (Sub (Twice x) y) sq i 'True 'True)
      ZeroC
      ('Complex (Sub y (Twice x)) sq i 'True 'False)
  ('Complex x sq i 'False 'True) :+: ('Complex y _ _ 'False 'True) =
    'Complex (Add x y) sq i 'False 'True
  ('Complex x sq i 'False 'True) :+: ('Complex y sq i 'False 'False) =
    Compare x y
      ('Complex (Sub x y) sq i 'False 'True)
      ZeroC
      ('Complex (Sub y x) sq i 'False 'False)
  ('Complex x sq i 'False 'False) :+: ('Complex y sq i 'True 'True) =
    Compare (Twice x) y
      ('Complex (Sub (Twice x) y) sq i 'True 'False)
      ZeroC
      ('Complex (Sub y (Twice x)) sq i 'True 'True)
  ('Complex x sq i 'False 'False) :+: ('Complex y sq i 'True 'False) =
    'Complex (Add (Twice x) y) sq i 'True 'False
  ('Complex x sq i 'False 'False) :+: ('Complex y sq i 'False 'True) =
    Compare x y
      ('Complex (Sub x y) sq i 'False 'False)
      ZeroC
      ('Complex (Sub y x) sq i 'False 'True)
  ('Complex x sq i 'False 'False) :+: ('Complex y sq i 'False 'False) =
    'Complex (Add x y) sq i 'False 'False

type family ComputeNat (x :: Nat) (y :: Nat) (sq1 :: Bool) (sq2 :: Bool) (h1 :: Bool) (h2 :: Bool) :: Nat where
  ComputeNat x y 'True 'True 'True 'True =
    MultN x y
  ComputeNat x y 'True 'True 'True 'False =
    MultN x y
  ComputeNat x y 'True 'True 'False 'True =
    MultN x y
  ComputeNat x y 'True 'True 'False 'False =
    Twice (MultN x y)
  ComputeNat x y 'True 'False 'True 'False =
    IfThenElse (Even y)
      (MultN x (Half y))
      (MultN x y)
  ComputeNat x y 'True 'False 'False 'True =
    IfThenElse (Even x)
      (MultN (Half x) y)
      (MultN x y)
  ComputeNat x y 'True 'False 'False 'False =
    MultN x y
  ComputeNat x y 'False 'True 'True 'False =
    IfThenElse (Even y)
      (MultN x (Half y))
      (MultN x y)
  ComputeNat x y 'False 'True 'False 'True =
    IfThenElse (Even x)
      (MultN (Half x) y)
      (MultN x y)
  ComputeNat x y 'False 'True 'False 'False =
    MultN x y
  ComputeNat x y 'False 'False 'True 'False =
    IfThenElse (Even y)
      (MultN x (Half y))
      (MultN x y)
  ComputeNat x y 'False 'False 'False 'True =
    IfThenElse (Even x)
      (MultN (Half x) y)
      (MultN x y)
  ComputeNat x y 'False 'False 'False 'False =
    MultN x y

type family ComputeHalf (x :: Nat) (y :: Nat) (sq1 :: Bool) (sq2 :: Bool) (h1 :: Bool) (h2 :: Bool) :: Bool where
  ComputeHalf x y 'True 'True 'True 'True =
    'True
  ComputeHalf x y 'True 'True 'True 'False =
    'False
  ComputeHalf x y 'True 'True 'False 'True =
    'False
  ComputeHalf x y 'True 'True 'False 'False =
    'False
  ComputeHalf x y 'True 'False 'True 'False =
    Odd y
  ComputeHalf x y 'True 'False 'False 'True =
    Odd x
  ComputeHalf x y 'True 'False 'False 'False =
    'False
  ComputeHalf x y 'False 'True 'True 'False =
    Odd y
  ComputeHalf x y 'False 'True 'False 'True =
    Odd x
  ComputeHalf x y 'False 'True 'False 'False =
    'False
  ComputeHalf x y 'False 'False 'True 'False =
    Odd y
  ComputeHalf x y 'False 'False 'False 'True =
    Odd x
  ComputeHalf x y 'False 'False 'False 'False =
    False

type family ComputeSign (i1 :: Bool) (i2 :: Bool) (m1 :: Bool) (m2 :: Bool) :: Bool where
  ComputeSign 'True 'True 'True 'True = 'True
  ComputeSign 'True 'True 'True 'False = 'False
  ComputeSign 'True 'True 'False 'True = 'False
  ComputeSign 'True 'True 'False 'False = 'True
  ComputeSign 'True 'False 'True 'True = 'False
  ComputeSign 'True 'False 'True 'False = 'True
  ComputeSign 'True 'False 'False 'True = 'True
  ComputeSign 'True 'False 'False 'False = 'False
  ComputeSign 'False 'True 'True 'True = 'False
  ComputeSign 'False 'True 'True 'False = 'True
  ComputeSign 'False 'True 'False 'True = 'True
  ComputeSign 'False 'True 'False 'False = 'False
  ComputeSign 'False 'False 'True 'True = 'False
  ComputeSign 'False 'False 'True 'False = 'True
  ComputeSign 'False 'False 'False 'True = 'True
  ComputeSign 'False 'False 'False 'False = 'False

type family MultC (m :: Complex) (n :: Complex) :: Complex where
  MultC ('Complex 'ZN _ _ _ _) _ = ZeroC
  MultC _ ('Complex 'ZN _ _ _ _) = ZeroC
  MultC ('Complex x sq1 i1 h1 m1) ('Complex y sq2 i2 h2 m2) =
    'Complex
      (ComputeNat x y sq1 sq2 h1 h2)
      (NEq sq1 sq2)
      (NEq i1 i2)
      (ComputeHalf x y sq1 sq2 h1 h2)
      (ComputeSign i1 i2 m1 m2)

-- * List related functions

data IsListC (l :: [Complex]) :: Type where
  IsN :: IsListC '[]
  IsC :: IsComplex x -> IsListC l -> IsListC (x ': l)

data IsListL (l :: [[Complex]]) :: Type where
  IsNL :: IsListL '[]
  IsCL :: IsListC x -> IsListL l -> IsListL (x ': l)

type family Length (l :: [a]) :: Nat where
  Length '[] = 'ZN
  Length (x ': tl) = 'SN (Length tl)

type family Get (l :: [a]) (n :: Nat) where
  Get (x ': tl) 'ZN = x
  Get (x ': tl) ('SN n) = Get tl n
