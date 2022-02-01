{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Matrix where

import Data.Kind ( Type )

import Bool
import Nat
import Complex
import List

-- * Matrices related functions

data Mat (a :: Type) :: Type where
  Mat :: [[a]] -> Mat a

data IsMat (f :: a -> Type) (m :: Mat a) :: Type where
  IsM :: IsList (IsList f) l -> IsMat f ('Mat l)

type family NbLines (m :: Mat a) :: Nat where
  NbLines ('Mat l) = Length l

type family NbCols (m :: Mat a) :: Nat where
  NbCols ('Mat (l ': _)) = Length l

type family Access (m :: Mat a) (l :: Nat) (c :: Nat) :: a where
  Access ('Mat lines) l c = Get (Get lines l) c

type family (×) (a :: Mat C) (b :: Mat C) :: Mat C where
  a × b = FillMatrix (PartialOneProd a b) (NbLines a) (NbCols b)

type family (⊗) (a :: Mat C) (b :: Mat C) :: Mat C where
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
    AuxFillMatrix f cMax ('SN l) 'ZN '[] (c ': lTl) =
      AuxFillMatrix f cMax l cMax ((c ': lTl) ': '[]) '[]
    AuxFillMatrix f cMax ('SN l) 'ZN (mHd ': mTl) (c ': lTl) =
      AuxFillMatrix f cMax l cMax ((c ': lTl) ': mHd ': mTl) '[]
    AuxFillMatrix f cMax ('SN l) ('SN c) mAcc '[] =
      AuxFillMatrix f cMax ('SN l) c mAcc (Apply2 f l c ': '[])
    AuxFillMatrix f cMax ('SN l) ('SN c) mAcc (hd ': lTl) =
      AuxFillMatrix f cMax ('SN l) c mAcc (Apply2 f l c ': hd ': lTl)

data Interleaved :: Mat C -> *
data DiagIM :: Mat C -> *
data PartialOneProd :: Mat C -> Mat C -> *
type family Apply2 (f :: *) (x :: k1) (y :: k2) :: k3 where
  Apply2 (PartialOneProd m1 m2) l c = AuxComputeOneProd m1 m2 (NbLines m2) l c 'ZN ZeroC (EqN 'ZN (NbLines m2))
  Apply2 (PartialOneTens m1 m2) l c = AuxComputeOneTens m1 m2 (Quo l (NbLines m2)) (Rem l (NbLines m2)) (Quo c (NbCols m2)) (Rem c (NbCols m2))
  Apply2 (Interleaved m) l c = AuxInterleaved m l c (Even l) (Even c)
  Apply2 (DiagIM m) l c = AuxDiagIM m l c (Geq l (NbLines m)) (Geq c (NbCols m))

type family AuxInterleaved (m :: Mat C) (l :: Nat) (c :: Nat) (evenL :: Bool) (evenC :: Bool) :: C where
  AuxInterleaved m l c 'True _ = IfThenElse (EqN l c) OneC ZeroC
  AuxInterleaved m l c 'False 'True = ZeroC
  AuxInterleaved m l c 'False 'False = Access m (Half (Pred l)) (Half (Pred c))

type family AuxDiagIM (m :: Mat C) (l :: Nat) (c :: Nat) (bigL :: Bool) (bigC :: Bool) :: C where
  AuxDiagIM m l c 'True 'True = Access m (SubN l (NbLines m)) (SubN c (NbCols m))
  AuxDiagIM m l c 'True 'False = ZeroC
  AuxDiagIM m l c 'False 'True = ZeroC
  AuxDiagIM m l c 'False 'False = IfThenElse (EqN l c) OneC ZeroC

type family AuxComputeOneProd
  (m1 :: Mat C)
  (m2 :: Mat C)
  (maxK :: Nat)
  (l :: Nat)
  (c :: Nat)
  (k :: Nat)
  (acc :: C)
  (termin :: Bool) :: C where
    AuxComputeOneProd m1 m2 maxK l c k acc 'True = acc
    AuxComputeOneProd m1 m2 maxK l c k acc 'False =
      AuxComputeOneProd m1 m2 maxK l c ('SN k)
        (AddC acc (MultC (Access m1 l k) (Access m2 k c)))
        (EqN maxK ('SN k))

data PartialOneTens :: Mat C -> Mat C -> *
type family AuxComputeOneTens
  (m1 :: Mat C)
  (m2 :: Mat C)
  (qL :: Nat)
  (rL :: Nat)
  (qC :: Nat)
  (rC :: Nat) :: C where
    AuxComputeOneTens m1 m2 qL rL qC rC =
      MultC (Access m1 qL qC) (Access m2 rL rC)

-- Here we assume that the 4x4 is a tensorial product.
type family UnsafeUntensor44 (m :: Mat C) :: (Mat C, Mat C) where
  UnsafeUntensor44 m =
    IfThenElse
      (IsNullC (Access m 'ZN 'ZN))
      (IfThenElse
        (IsNullC (Access m 'ZN OneN))
        (IfThenElse
          (IsNullC (Access m 'ZN TwoN))
          ('(,)
            ('Mat
              ((ZeroC ': OneC ': '[]) ':
              (MultC (Access m TwoN OneN) (InvC (Access m 'ZN ThreeN)) ': MultC (Access m TwoN ThreeN) (InvC (Access m 'ZN ThreeN)) ': '[]) ':
              '[]
              )
            )
            ('Mat ((ZeroC ': Access m 'ZN ThreeN ': '[]) ': (Access m OneN TwoN  ': Access m OneN ThreeN ': '[]) ': '[]))
          )
          ('(,)
            ('Mat
              ((ZeroC ': OneC ': '[]) ':
              (MultC (Access m TwoN 'ZN) (InvC (Access m 'ZN TwoN)) ': MultC (Access m TwoN TwoN) (InvC (Access m 'ZN TwoN)) ': '[]) ':
              '[]
              )
            )
            ('Mat ((Access m 'ZN TwoN ': Access m 'ZN ThreeN ': '[]) ': (Access m OneN TwoN  ': Access m OneN ThreeN ': '[]) ': '[]))
          )
        )
        ('(,)
          ('Mat
            ((OneC ': MultC (Access m 'ZN ThreeN) (InvC (Access m 'ZN OneN)) ': '[]) ':
            (MultC (Access m TwoN OneN) (InvC (Access m 'ZN OneN)) ': MultC (Access m TwoN ThreeN) (InvC (Access m 'ZN OneN)) ': '[]) ':
            '[]
            )
          )
          ('Mat ((ZeroC ': Access m 'ZN OneN ': '[]) ': (Access m OneN 'ZN  ': Access m OneN OneN ': '[]) ': '[]))
        )
      )
      ('(,)
        ('Mat
          ((OneC ': MultC (Access m 'ZN TwoN) (InvC (Access m 'ZN 'ZN)) ': '[]) ':
          (MultC (Access m TwoN 'ZN) (InvC (Access m 'ZN 'ZN)) ': MultC (Access m TwoN TwoN) (InvC (Access m 'ZN 'ZN)) ': '[]) ':
          '[]
          )
        )
        ('Mat ((Access m 'ZN 'ZN ': Access m 'ZN OneN ': '[]) ': (Access m OneN 'ZN  ': Access m OneN OneN ': '[]) ': '[]))
      )

type family AddFirstLine (l :: [a]) (m :: Mat a) :: Mat a where
  AddFirstLine l ('Mat tl) = 'Mat (l ': tl)

type family NormalizeListC (m :: [C]) :: [C] where
  NormalizeListC '[] = '[]
  NormalizeListC (x ': tl) = NormalizeC x ': NormalizeListC tl

type family NormalizeMatC (m :: Mat C) :: Mat C where
  NormalizeMatC ('Mat '[]) = 'Mat '[]
  NormalizeMatC ('Mat (x ': tl)) =
    AddFirstLine (NormalizeListC x) (NormalizeMatC ('Mat tl))
