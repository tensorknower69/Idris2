module Compat.Prelude.Interfaces

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import Prelude.Ops

%default total

infixr 4 $>, <$

||| Run something for effects, replacing the return value with a given parameter.
public export
(<$) : Functor f => b -> f a -> f b
(<$) b = map (const b)

||| Flipped version of `<$`.
public export
($>) : Functor f => f a -> b -> f b
($>) fa b = map (const b) fa

||| Bifunctors
||| @f The action of the Bifunctor on pairs of objects
public export
interface Bifunctor f where
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> c) -> (b -> d) -> f a b -> f c d
  bimap f g = mapFst f . mapSnd g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| mapFst (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  mapFst : (a -> c) -> f a b -> f c b
  mapFst f = bimap f id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| mapSnd reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  mapSnd : (b -> d) -> f a b -> f a d
  mapSnd = bimap id

public export
mapHom : Bifunctor f => (a -> b) -> f a a -> f b b
mapHom f = bimap f f


public export
Semigroup () where
  _ <+> _ = ()

public export
Monoid () where
  neutral = ()
