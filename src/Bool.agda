module Bool where

open import 1Lab.Prelude hiding (Bool)

data Bool : Type where
  true : Bool
  false : Bool

and : Bool -> Bool -> Bool
and true true = true
and true false = false
and false true = false
and false false = false

and-false-is-false :
  (x : Bool) →
  and false x ≡ false
and-false-is-false true = refl
and-false-is-false false = refl
