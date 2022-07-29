{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

-- |
--
-- This library is a solution for the problem of partially filled data structure.
--
-- For example, consider the following type:
--
-- >>> :set -XDeriveGeneric -XTypeApplications -XDataKinds -XTypeFamilies
-- >>> import Data.Function ((&))
-- >>> :{
-- data Example = Example
--   { field1 :: Int,
--     field2 :: String
--   }
--   deriving (Generic, Show)
-- :}
--
-- You may want to provide a "default" value, with some fields which does not contain a default value. Most people are solving this using:
--
-- >>> defExample = Example { field1 = 10, field2 = error "You must set field 2" }
--
-- And later, at call site:
--
-- >>> defExample { field2 = "And now a value" }
-- Example {field1 = 10, field2 = "And now a value"}
--
-- This approach comes with a few limitations:
--
-- - You may forget to fill the missing fields, hence leading to an exception at runtime
-- - User are not aware that they need to fill the field
-- - This pattern is not usable with `StrictData`.
--
-- There are countless alternatives. For example, you may want to define a function such as:
--
-- >>> defaultExampleWithField2 s = Example 10 s
--
-- However, this approach does not scale with the number of field, and the naming
-- is not explicit at all.
--
-- This library tries to solve this problem by letting you fill an anonymous record which will only be convertible when all the fields has been correctly filled:
--
-- - It is type safe, you cannot go wrong.
-- - You address the field by their name, hence it's explicit.
-- - Errors message should be acceptable (once the `TypeError` would have been added where needed)
--
--
-- For example, the previous example can be written such as:
--
-- >>> :{
-- >>> defExample = ((emptyIncompletRep :: IncompleteRep (Rep Example) x)
--     & fillAField2 (Proxy @"field1") (10 :: Int)
--     )
-- :}
--
-- >>> (defExample & fillAField2 (Proxy @"field2") "Salut" & finish) :: Example
-- Example {field1 = 10, field2 = "Salut"}
module PartialBuilder
  ( emptyIncompletRep,
    fillAField2,
    finish,
    IncompleteRep,
    Rep,
  )
where

import Data.Data (Proxy (Proxy))
import Data.Function ((&))
import GHC.Generics
import GHC.TypeLits (Symbol)

-- | That's a placeholder for a future value, which is not yet known.
data Incomplete t = Incomplete
  deriving (Show)

-- | @'IncompleteRep ('Rep t)@ represents a record where all fields @t'@ are replaced by @'Incomplete t'@
type family IncompleteRep x where
  IncompleteRep (S1 s (Rec0 t)) = S1 s (Rec0 (Incomplete t))
  IncompleteRep (M1 x y v) = M1 x y (IncompleteRep v)
  IncompleteRep (a :*: b) = IncompleteRep a :*: IncompleteRep b

-- | Build a 'Rep' which contains 'Incomplete' in all field values.
class EmptyIncompleteRep f where
  emptyIncompletRep :: f x

instance EmptyIncompleteRep z => EmptyIncompleteRep (M1 x y z) where
  emptyIncompletRep = M1 emptyIncompletRep

instance (EmptyIncompleteRep a, EmptyIncompleteRep b) => EmptyIncompleteRep (a :*: b) where
  emptyIncompletRep = emptyIncompletRep :*: emptyIncompletRep

instance EmptyIncompleteRep (K1 i (Incomplete c)) where
  emptyIncompletRep = K1 Incomplete

-- | Locate the "path" in a 'Rep' toward a field.
type family PathToField (fieldName :: Symbol) x where
  PathToField fieldName (D1 x z) = PathToField fieldName z
  PathToField fieldName (C1 x z) = PathToField fieldName z
  PathToField fieldName (S1 ('MetaSel ('Just fieldName) _ _ _) t) = Just '[]
  PathToField fieldName (a :*: b) = PathThatMatch (PathToField fieldName a) (PathToField fieldName b)
  PathToField fieldName t = Nothing

type family PathThatMatch (a :: Maybe [Direction]) (b :: Maybe [Direction]) :: Maybe [Direction] where
  PathThatMatch (Just p) Nothing = Just (LL ': p)
  PathThatMatch Nothing (Just p) = Just (RR ': p)

data Direction = LL | RR

type family FromJust x where
  FromJust (Just x) = x

-- | Replace an 'Incomplete' for a specific 'path' with the correct value.
class SetIncomplete path v f f' | path v f -> f' where
  setIncomplete :: Proxy path -> v -> f x -> f' x

instance (M1 x y z' ~ f', SetIncomplete p v z z') => SetIncomplete p v (M1 x y z) f' where
  setIncomplete path v (M1 x) = M1 (setIncomplete path v x)

instance (a' :*: b ~ f', SetIncomplete path v a a') => SetIncomplete (LL ': path) v (a :*: b) f' where
  setIncomplete Proxy v (a :*: b) = setIncomplete (Proxy @path) v a :*: b

instance (a :*: b' ~ f', SetIncomplete path v b b') => SetIncomplete (RR ': path) v (a :*: b) f' where
  setIncomplete Proxy v (a :*: b) = a :*: setIncomplete (Proxy @path) v b

instance (Rec0 v ~ f') => SetIncomplete '[] v (Rec0 (Incomplete v)) f' where
  setIncomplete Proxy v (K1 Incomplete) = K1 v

fillAField2 :: forall (fieldName :: Symbol) v f f' x path. (path ~ FromJust (PathToField fieldName f), SetIncomplete path v f f') => Proxy fieldName -> v -> f x -> f' x
fillAField2 Proxy = setIncomplete (Proxy @path)

-- | Finish an incomplete type, only if all required fields are specified.
finish :: Generic a => Rep a x -> a
finish = to

data Example = Example
  { field1 :: Int,
    field2 :: String
  }
  deriving (Generic, Show)

defExample :: Example
defExample =
  (emptyIncompletRep :: IncompleteRep (Rep Example) x)
    & fillAField2 (Proxy @"field1") (10 :: Int)
    & fillAField2 (Proxy @"field2") "Salut"
    & finish
