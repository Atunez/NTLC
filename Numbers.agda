module Numbers where

data Nat : Set where
    O : Nat
    S : Nat → Nat

_++_ : Nat → Nat → Nat
O ++ m = m
S n ++ m = S (n ++ m)

