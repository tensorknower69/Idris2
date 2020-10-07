module Compat.Data.Vect

import Data.Vect

%default total

public export
toVect : (n : Nat) -> List a -> Maybe (Vect n a)
toVect Z [] = Just []
toVect (S k) (x :: xs)
    = do xs' <- toVect k xs
         pure (x :: xs')
toVect _ _ = Nothing
