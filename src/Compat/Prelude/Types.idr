module Compat.Prelude.Types

import Compat.Prelude.Interfaces

%default total

%inline
public export
Bifunctor Pair where
  bimap f g (x, y) = (f x, g y)

%inline
public export
Bifunctor Either where
  bimap f _ (Left x) = Left (f x)
  bimap _ g (Right y) = Right (g y)
