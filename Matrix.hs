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

type family IsMatC (m :: Mat C) :: Type where
  IsMatC m = IsMat IsC m

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
    AuxFillMatrix f cMax ('SN l) 'ZN accMat accLine =
      AuxFillMatrix f cMax l cMax (accLine ': accMat) '[]
    AuxFillMatrix f cMax ('SN l) ('SN c) mAcc accLine =
      AuxFillMatrix f cMax ('SN l) c mAcc (Apply2 f l c ': accLine)

data PartialOneControl :: Mat C -> *
data PartialOneProd :: Mat C -> Mat C -> *
type family Apply2 (f :: *) (x :: k1) (y :: k2) :: k3 where
  Apply2 (PartialOneProd m1 m2) l c = AuxComputeOneProd m1 m2 (NbLines m2) l c 'ZN ZeroC (EqN 'ZN (NbLines m2))
  Apply2 (PartialOneTens m1 m2) l c = AuxComputeOneTens m1 m2 (Quo l (NbLines m2)) (Rem l (NbLines m2)) (Quo c (NbCols m2)) (Rem c (NbCols m2))
  Apply2 (PartialOneControl m) l c = AuxComputeOneControl m l c (Geq l (NbLines m)) (Geq c (NbCols m))

type family AuxComputeOneControl (m :: Mat C) (l :: Nat) (c :: Nat) (bigL :: Bool) (bigC :: Bool) :: C where
  AuxComputeOneControl m l c 'True 'True = Access m (SubN l (NbLines m)) (SubN c (NbCols m))
  AuxComputeOneControl m l c 'True 'False = ZeroC
  AuxComputeOneControl m l c 'False 'True = ZeroC
  AuxComputeOneControl m l c 'False 'False = IfThenElse (EqN l c) OneC ZeroC

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
type family UnsafeUntensor44 (m :: Mat C) :: (Mat C, (Mat C, C)) where
  UnsafeUntensor44 m =
    UnsafeUntensor44Null00 (IsNullC (Access m 'ZN 'ZN)) m

type family UnsafeUntensor44Null00 (b :: Bool) (m :: Mat C) :: (Mat C, (Mat C, C)) where
  UnsafeUntensor44Null00 'True m =
    UnsafeUntensor44Null01 (IsNullC (Access m 'ZN OneN)) m
  UnsafeUntensor44Null00 'False m =
    '(,)
      ('Mat
        ( (OneC ': DivC (Access m 'ZN TwoN) (Access m 'ZN 'ZN) ': '[]) ':
          (DivC (Access m TwoN 'ZN) (Access m 'ZN 'ZN) ': DivC (Access m TwoN TwoN) (Access m 'ZN 'ZN) ': '[]) ':
        '[]
        )
      )
      ('(,)
        ('Mat
          ( (OneC ': DivC (Access m 'ZN OneN) (Access m 'ZN 'ZN) ': '[]) ':
            (DivC (Access m OneN 'ZN) (Access m 'ZN 'ZN)  ': DivC (Access m OneN OneN) (Access m 'ZN 'ZN) ': '[]) ':
            '[]
          )
        )
        (Access m 'ZN 'ZN)
      )

type family UnsafeUntensor44Null01 (b :: Bool) (m :: Mat C) :: (Mat C, (Mat C, C)) where
  UnsafeUntensor44Null01 'True m =
    UnsafeUntensor44Null02 (IsNullC (Access m 'ZN TwoN)) m
  UnsafeUntensor44Null01 'False m =
    '(,)
      ('Mat
        ( (OneC ': DivC (Access m 'ZN ThreeN) (Access m 'ZN OneN) ': '[]) ':
          (DivC (Access m TwoN OneN) (Access m 'ZN OneN) ': DivC (Access m TwoN ThreeN) (Access m 'ZN OneN) ': '[]) ':
          '[]
        )
      )
      ('(,)
        ('Mat
          ( (ZeroC ': OneC ': '[]) ':
            (DivC (Access m OneN 'ZN) (Access m 'ZN OneN)  ': DivC (Access m OneN OneN) (Access m 'ZN OneN) ': '[]) ':
            '[]
          )
        )
        (Access m 'ZN OneN)
      )

type family UnsafeUntensor44Null02 (b :: Bool) (m :: Mat C) :: (Mat C, (Mat C, C)) where
  UnsafeUntensor44Null02 'True m =
    '(,)
      ('Mat
        ( (ZeroC ': OneC ': '[]) ':
          (DivC (Access m TwoN OneN) (Access m 'ZN ThreeN) ': DivC (Access m TwoN ThreeN) (Access m 'ZN ThreeN) ': '[]) ':
          '[]
        )
      )
      ('(,)
        ('Mat
          ( (ZeroC ': OneC ': '[]) ':
            (DivC (Access m OneN TwoN) (Access m 'ZN ThreeN)  ': DivC (Access m OneN ThreeN) (Access m 'ZN ThreeN) ': '[]) ':
            '[]
          )
        )
        (Access m 'ZN ThreeN)
      )
  UnsafeUntensor44Null02 'False m =
    '(,)
      ('Mat
        ( (ZeroC ': OneC ': '[]) ':
          (DivC (Access m TwoN 'ZN) (Access m 'ZN TwoN) ': DivC (Access m TwoN TwoN) (Access m 'ZN TwoN) ': '[]) ':
          '[]
        )
      )
      ('(,)
        ('Mat
          ( (OneC ': DivC (Access m 'ZN ThreeN) (Access m 'ZN TwoN) ': '[]) ':
            (DivC (Access m OneN TwoN) (Access m 'ZN TwoN)  ': DivC (Access m OneN ThreeN) (Access m 'ZN TwoN) ': '[]) ':
            '[]
          )
        )
        (Access m 'ZN TwoN)
      )

type family UnsafeUntensor44Type (m :: Mat C) :: Type where
  UnsafeUntensor44Type m = UnsafeUntensor44TypeAux (UnsafeUntensor44 m)
type family UnsafeUntensor44TypeAux (t :: (Mat C, (Mat C, C))) :: Type where
  UnsafeUntensor44TypeAux ('(,) m1 ('(,) m2 c)) = (IsMatC m1, IsMatC m2, IsC c)

type family AddFirstLine (l :: [a]) (m :: Mat a) :: Mat a where
  AddFirstLine l ('Mat tl) = 'Mat (l ': tl)

type family NormalizeListC (m :: [C]) :: [C] where
  NormalizeListC '[] = '[]
  NormalizeListC (x ': tl) = NormalizeC x ': NormalizeListC tl

type family NormalizeMatC (m :: Mat C) :: Mat C where
  NormalizeMatC ('Mat '[]) = 'Mat '[]
  NormalizeMatC ('Mat (x ': tl)) =
    AddFirstLine (NormalizeListC x) (NormalizeMatC ('Mat tl))

type family OneHeaded (m :: Mat C) :: (Mat C, C) where
  OneHeaded m = ExtractHead '[] '[] (NormalizeMatC m)
type family ExtractHead (accLine :: [C]) (accPrevLines :: [[C]]) (m :: Mat C) :: (Mat C, C) where
  ExtractHead accLine accPrevLines ('Mat ('[] ': tl)) =
    ExtractHead '[] (accLine ': accPrevLines) ('Mat tl)
  ExtractHead accLine accPrevLines ('Mat ((hd ': tlCurrLines) ': tlNextLines)) =
    ExtractHeadAux (IsNullC hd) accLine accPrevLines hd tlCurrLines tlNextLines

type family ExtractHeadAux (b :: Bool) (accLine :: [C]) (accPrevLines :: [[C]])
  (hd :: C) (tlCurrLines :: [C]) (tlNextLines :: [[C]]) :: (Mat C, C) where
    ExtractHeadAux 'True accLine accPrevLines _ tlCurrLines tlNextLines =
      ExtractHead (ZeroC ': accLine) accPrevLines ('Mat (tlCurrLines ': tlNextLines))
    ExtractHeadAux 'False accLine accPrevLines hd tlCurrLines tlNextLines =
      '(,)
        ('Mat
          (Concat accPrevLines
            (Concat accLine (OneC ': DivideLine hd tlCurrLines) ':
              DivideMat hd tlNextLines
            )
          )
        )
        hd

type family OneHeadedType (m :: Mat C) :: Type where
  OneHeadedType m = OneHeadedTypeAux (OneHeaded m)
type family OneHeadedTypeAux (t :: (Mat C, C)) :: Type where
  OneHeadedTypeAux ('(,) m c) = (IsMatC m, IsC c)

type family DivideMat (x :: C) (l :: [[C]]) :: [[C]] where
  DivideMat x '[] = '[]
  DivideMat x (hd ': tl) = DivideLine x hd ': DivideMat x tl
type family DivideLine (x :: C) (l :: [C]) :: [C] where
  DivideLine x '[] = '[]
  DivideLine x (hd ': tl) = DivC hd x ': DivideLine x tl

type family MatrixControl (m :: Mat C) :: Mat C where
  MatrixControl m = FillMatrix (PartialOneControl m) (Twice (NbLines m)) (Twice (NbCols m))
