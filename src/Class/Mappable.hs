{-|
Module: Class.Mappable
Description: Map functions over data as polymorphically as possible.
License: 0BSD
Maintainer: wygulmage@users.noreply.github.com
Stability: Experimental
Portability: GHC

'Mappable' lets you 'map' over various structures. It's intended to unify all the functions named @map@ ('Data.List.map', 'Data.Set.map', 'Data.Text.map', etc.). To do this it uses type families.
'Data.Functor.Functor' and 'Data.MonoTraversable.MonoFunctor' provide simpler interfaces. But, 'Functor' 'fmap' requires a fully polymorphic container, while 'Data.MonoTraversable.MonoFunctor' 'Data.MonoTraversable.omap' can only map with endofunctions (and neither provides 'mapCoerce' yet).
-}

{-# LANGUAGE NoImplicitPrelude
           , ScopedTypeVariables
           , TypeFamilies
           , UndecidableInstances
           , FlexibleContexts
           , FlexibleInstances
           , DefaultSignatures
           , RankNTypes
           , MultiParamTypeClasses
           , GeneralizedNewtypeDeriving
   #-}


module Class.Mappable (
Mappable (..), omap,
ValidMorph,
WrapMappable (..),
WrapFunctor (..),
) where


import Control.Arrow (Arrow)
import Control.Applicative
import Control.Monad (Monad)
import Control.Monad.ST (ST)
import qualified Control.Exception as Exception
import Data.Ord
import Data.Semigroup
import qualified Data.Semigroup as Semigroup
import qualified Data.Monoid as Monoid
import qualified Data.Functor as Data
import Data.Bool (Bool)
import Data.Char
import Data.Int (Int)
import Data.Word (Word8)
import qualified Data.ByteString as Bytes
import qualified Data.ByteString.Lazy as Lazy.Bytes
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy.Text
import qualified Data.Sequence as Seq
import qualified Data.Tree as Rose
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.Complex
import Data.Tagged
import Data.Maybe (Maybe)
import Data.Either
import Data.Proxy
import Data.Functor.Identity
import qualified Data.List.NonEmpty as NonEmpty
import Data.Coerce (Coercible, coerce)
import Data.Kind

import GHC.Arr (Array)
import GHC.Conc (STM)

import Prelude (IO)

import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)


newtype WrapFunctor m a = WrapFunctor (m a)
   deriving (Data.Functor, Applicative, Alternative, Monad)

newtype WrapMappable t = WrapMappable t


type family ObjectDefault (ma :: Type) where ObjectDefault (m (a :: Type)) = a
{- ^ the rightmost parameter of a type -}

type family MorphDefault (x :: Type) (y :: Type) where
   MorphDefault (polymorphic a) b = polymorphic b
   MorphDefault monomorphic b     = monomorphic
{- ^ Try to replace the rightmost parameter of a type. If the type is polymorphic, the rightmost parameter is replaced; otherwise the original type is returned. -}

class    (Object (Morph mb a) ~ a)=> ValidMorph (mb :: Type) (a :: Type)
instance (Object (Morph mb a) ~ a)=> ValidMorph (mb :: Type) (a :: Type)

class (Morph mb (Object mb) ~ mb)=> Mappable (mb :: Type) where
{-^ @Mappable@ extends the power of 'Functor' to monomorphic containers and containers that constrain their contents.
To create an instance of @Mappable@ for a 'Functor', write e.g. @instance Mappable [b]@.
To create an instance of @Mappable@ for a monomorphic type, write e.g.
@instance Mappable 'Text.Text' where
   type Object 'Text.Text' = 'Char'
   'map' = 'Text.map'
@
To create an instance for a type that constraints its objects, you need to include a definition of 'mapCoerce'.
@instance (Ord b)=> Mappable ('Set.Set' b) where
   'map' = 'Set.map'
   'mapCoerce' = 'map' 'coerce'
@
To define an instance where the 'Object' is phantom, use a kind annotation: @instance Mappable ('Proxy' (o :: 'Type'))@.

Laws:
   1. for all f g. @map (g '$!') . map f@ === @map ((g '$!') . f)@, as long as equal ('==') objects produced by @f@ are indistinguishable to 'g'.
   2. @map 'id'@ === 'id'
   3. 'mapCoerce' === @'map' 'coerce'@
The first law forces @g@'s argument to accommodate both strict and lazy containers, and has the condition on equal objects to accommodate both 'Arg' and 'Set.Set'.
-}
   type Morph mb (a :: Type) :: Type
   {-^ Try to change the type of an object in a container. @Morph [a] b = [b]@; @Morph 'Text.Text' b = 'Text.Text'. -}
   type Morph mb a = MorphDefault mb a
   type Object mb :: Type
   {-^ The type of the objects in the container. By default it's the type's rightmost parameter. -}
   type Object mb = ObjectDefault mb

   map ::
      forall a. (ValidMorph mb a)=>
      (a -> Object mb) -> Morph mb a -> mb
   {-^ Map a function over all the 'Object's in a container. -}

   mapCoerce ::
      forall a. (ValidMorph mb a, Coercible a (Object mb))=>
      Morph mb a -> mb
   {-^ Coerce all the 'Object's in a container to a new type. -}
   -- mapCoerce = map coerce

   default map ::
      (ValidMorph mb a, Morph mb a ~ m a, m (Object mb) ~ mb, Data.Functor m)=>
      (a -> Object mb) -> Morph mb a -> mb
   map = Data.fmap
   {-# INLINE map #-}

   default mapCoerce ::
      (ValidMorph mb a, Coercible (Morph mb a) mb)=> Morph mb a -> mb
   mapCoerce = coerce
   {-# INLINE mapCoerce #-}


omap :: (Mappable t)=> (Object t -> Object t) -> t -> t
omap = map
{-# INLINE omap #-}

------ Instances ------

-- TODO: Add instances for lifted `Functor`s (e.g. `Ap m b`). Should these rely on the `Functor` instance or the `Mappable` instance? In favor of `Mappble` is being able to use constrained containers like `Set`.

--- State Functors ---
instance Mappable (IO b)
instance Mappable (ST s b)
instance Mappable (STM b)

--- Empty Containers ---
instance Mappable (Proxy (b :: Type))

--- Identity Containers ---
instance Mappable (Identity b)
instance Mappable (Down b)
instance Mappable (Dual b)
instance Mappable (Semigroup.First b)
instance Mappable (Semigroup.Last b)
instance Mappable (Max b)
instance Mappable (Min b)
instance Mappable (Product b)
instance Mappable (Sum b)

instance Mappable Semigroup.All where
   type Object Semigroup.All = Bool
   map = coerce

instance Mappable Semigroup.Any where
   type Object Semigroup.Any = Bool
   map = coerce


--- Affine Containers ---
instance Mappable (Maybe b)
instance Mappable (Monoid.First b)
instance Mappable (Monoid.Last b)

--- Fixed-size Vectors ---
instance Mappable (Complex b)

--- Sequences ---
instance Mappable [b]
instance Mappable (ZipList b)

instance Mappable (NonEmpty.NonEmpty b)

instance Mappable (Seq.Seq b)
instance Mappable (Seq.ViewL b)
instance Mappable (Seq.ViewR b)

instance Mappable (Rose.Tree b)

instance Mappable (Array i b)

instance Mappable Bytes.ByteString where
   type Object Bytes.ByteString = Word8
   map = Bytes.map

instance Mappable Lazy.Bytes.ByteString where
   type Object Lazy.Bytes.ByteString = Word8
   map = Lazy.Bytes.map

instance Mappable Text.Text where
   type Object Text.Text = Char
   map = Text.map

instance Mappable Lazy.Text.Text where
   type Object Lazy.Text.Text = Char
   map = Lazy.Text.map

--- Sets ---
instance (Ord b)=> Mappable (Set.Set b) where
   map = Set.map
   mapCoerce = map coerce
{-^ WARNING: @map (g $!) . map f@ is not equivalent to @map ((g $!) . f)@ when @g@ can distinguish between different but equal ('==') values produced by @f@. For example, @map (\ ('Arg' () n) -> n) . map ('Arg' ())@ is likely to give a very different result than @map ((\ ('Arg' () n) -> n) . 'Arg' ())@. -}

instance Mappable IntSet.IntSet where
   type Object IntSet.IntSet = Int
   map = IntSet.map

--- Bifunctors ---
instance Mappable (Const c (b :: Type))

instance Mappable (Tagged c b)

instance Mappable (Either c b)

instance Mappable (c, b)
instance Mappable (Arg c b)

--- Functions ---
instance Mappable (a -> b)

instance Mappable (Exception.Handler b)

instance Mappable (ReadP b)
instance Mappable (ReadPrec b)

--- Maps ---
instance Mappable (Map.Map i b)
instance Mappable (IntMap.IntMap b)

--- Wrapped Instances ---
instance (Arrow p)=> Mappable (WrappedArrow p c b) where
   mapCoerce = map coerce

instance (Data.Functor m)=> Mappable (WrapFunctor m a) where
   mapCoerce = map coerce

instance (Mappable t)=> Mappable (WrapMappable t) where
   type Object (WrapMappable t) = Object t
   type Morph (WrapMappable t) a = WrapMappable (Morph t a)
   map f (WrapMappable xs) = WrapMappable (map f xs)
   mapCoerce (WrapMappable xs) = WrapMappable (mapCoerce xs)
