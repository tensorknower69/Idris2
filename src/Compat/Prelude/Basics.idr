module Compat.Prelude.Basics

%default total

||| Non-dependent if-then-else
public export
ifThenElse : (1 b : Bool) -> Lazy a -> Lazy a -> a
ifThenElse True l r = l
ifThenElse False l r = r
