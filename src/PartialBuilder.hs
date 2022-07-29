{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

module PartialBuilder where

import Data.Kind
import GHC.Generics
import GHC.TypeLits (Symbol)
import Data.Function ((&))
import Data.Data (Proxy (Proxy))

data HList (x :: [(Symbol, Type)]) where
  HNil :: HList '[]
  HCons :: Proxy tName -> a -> HList as -> HList ('(tName, a) ': as)

-- deriving instance Show (HList '[])
-- deriving instance (Show a, Show (HList xs)) => Show (HList ('(tName, a) ': xs))

newtype PartialBuilder (t :: Type) (remainingFields :: [(Symbol, Type)]) (knownFields :: [(Symbol, Type)]) = PartialBuilder (HList knownFields)
  -- deriving (Show)

type family AllFields t where
  AllFields t = GAllFields (Rep t)

type family GAllFields t :: [(Symbol, Type)] where
  GAllFields (D1 _ v) = GAllFields v
  GAllFields (C1 _ v) = GAllFields v
  GAllFields (a :*: b) = AppendList (GAllFields a) (GAllFields b)
  GAllFields (S1 ('MetaSel ('Just fieldName) _ _ _) (Rec0 t)) = '[ '(fieldName, t)]

data Status = Empty | Used

data Node k v where
  EmptyNode :: Node k Empty
  UsedNode :: k -> Node k Used

data Tree a b where
  Tree :: a -> b -> Tree a b

type family AppendList a b where
  AppendList '[] b = b
  AppendList (x ': xs) b = AppendList xs (x ': b)

emptyPartialBuilder :: PartialBuilder t (AllFields t) '[]
emptyPartialBuilder = PartialBuilder HNil

data Example = Example
  { field1 :: Int,
    field2 :: String
  }
  deriving (Generic, Show)

type family ExtractT (tName :: Symbol) (t :: Type) (remainingFields :: [(Symbol, Type)]) :: [(Symbol, Type)] where
  ExtractT tName t ('(tName, t) ': xs) = xs
  ExtractT tName t (x ': xs) = x ': ExtractT tName t xs

fillAField :: forall tName t remainingFields knownFields ti. ti -> PartialBuilder t remainingFields knownFields -> PartialBuilder t (ExtractT tName ti remainingFields) ('(tName, ti) ': knownFields)
fillAField newValue (PartialBuilder values) = PartialBuilder (HCons (Proxy @tName) newValue values)


type Yoto = ExtractT "field1" Int '[ '("field1", Int), '("field2", [Char]), '("field3", String)]
type Yotu = ExtractT "field2" Int '[ '("field1", Int), '("field2", [Char]), '("field3", String)]

val = emptyPartialBuilder
        & fillAField @"field1" (10 :: Int)
        & fillAField @"field2" "Salut"

type family EqualList a b where
  EqualList '[] '[] = 'True
  EqualList (x ': xs) ys = EqualList xs (PopItem x ys)

type family PopItem x l where
  PopItem x (x ': xs) = xs
  PopItem x (y ': xs) = y ': PopItem x xs

-- finish :: (EqualList (AllFields t) allFields ~ 'True, Generic t, RebuildFromFields (Rep t x0)) => PartialBuilder t '[] allFields -> t
-- finish (PartialBuilder fields) = to (fromFields fields)
-- 
-- class RebuildFromFields rep where
--   fromFields :: HList x -> rep

type family IncompleteRep x where
  IncompleteRep (D1 x v) = D1 x (IncompleteRep v)
  IncompleteRep (C1 x v) = C1 x (IncompleteRep v)
  IncompleteRep (a :*: b) = IncompleteRep a :*: IncompleteRep b
  IncompleteRep (S1 s (Rec0 t)) = S1 s (Rec0 (Incomplete t))

class EmptyIncompleteRep f where
  emptyIncompletRep :: f x

instance EmptyIncompleteRep z => EmptyIncompleteRep (M1 x y z) where
  emptyIncompletRep = M1 emptyIncompletRep

instance (EmptyIncompleteRep a, EmptyIncompleteRep b) => EmptyIncompleteRep (a :*: b) where
  emptyIncompletRep = emptyIncompletRep :*: emptyIncompletRep

instance EmptyIncompleteRep (K1 i (Incomplete c)) where
  emptyIncompletRep = K1 Incomplete

data Incomplete t = Incomplete
  deriving (Show)

type family PathToField (fieldName :: Symbol) x where
  PathToField fieldName (D1 x z) = PathToField fieldName z
  PathToField fieldName (C1 x z) = PathToField fieldName z
  PathToField fieldName (S1 ('MetaSel ('Just fieldName) _ _ _)  t) = Just '[]
  PathToField fieldName (a :*: b) = PathThatMatch (PathToField fieldName a) (PathToField fieldName b)
  PathToField fieldName t = Nothing

type family PathThatMatch (a :: Maybe [Direction]) (b :: Maybe [Direction]) :: Maybe [Direction] where
  PathThatMatch (Just p) Nothing = Just (LL ': p)
  PathThatMatch Nothing (Just p) = Just (RR ': p)

data Direction = LL | RR

type Tru = PathToField "field1" (Rep Example)
type Tru2 = PathToField "field2" (Rep Example)

type family FromJust x where
  FromJust (Just x) = x

class SetIncomplete path v f f' | path v f -> f' where
  setIncomplete :: Proxy path -> v -> f x -> f' x

instance SetIncomplete p v z z' => SetIncomplete p v (M1 x y z) (M1 x y z') where
  setIncomplete path v (M1 x) = M1 (setIncomplete path v x)

instance SetIncomplete path v a a' => SetIncomplete (LL ': path) v (a :*: b) (a' :*: b) where
  setIncomplete Proxy v (a :*: b) = setIncomplete (Proxy @path) v a :*: b

instance SetIncomplete path v b b' => SetIncomplete (RR ': path) v (a :*: b) (a :*: b') where
  setIncomplete Proxy v (a :*: b) = a :*: setIncomplete (Proxy @path) v b

instance SetIncomplete '[] v (Rec0 (Incomplete v)) (Rec0 v) where
  setIncomplete Proxy v (K1 Incomplete) = K1 v

a :: IncompleteRep (Rep Example) x
a = emptyIncompletRep

b = setIncomplete (Proxy @(FromJust Tru)) (10 :: Int) a

c = setIncomplete (Proxy @(FromJust Tru2)) "hello" b


finish :: Generic a => Rep a x -> a
finish = to

val' :: Example
val' = (emptyIncompletRep :: IncompleteRep (Rep Example) x)
        & fillAField2 (Proxy @"field1") (10 :: Int)
        & fillAField2 (Proxy @"field2") "Salut"
        & finish

fillAField2 :: forall (fieldName :: Symbol) v f f' x path. (path ~ FromJust (PathToField fieldName f), SetIncomplete path v f f') => Proxy fieldName -> v -> f x -> f' x
fillAField2 Proxy = setIncomplete (Proxy @path)
