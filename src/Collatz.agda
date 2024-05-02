module Collatz where

open import 1Lab.Prelude
open import 1Lab.Type.Pi
open import Data.Nat.Properties
open import Data.Nat.Base
open import Data.Nat.Solver using (nat!)

open import Bin

-- This will have properties
-- I'll want to study
-- For example, if this results
-- in a string of trailing 1s, then it's
-- guarenteed to shrink the string
-- when we add 1
bin-*3 : Bin D1 → Bin D1
bin-*3 x = bin-add x (B D0 x)

bin-*3≡*3 : {b : Bin D1} →
  bin→nat (D1 , bin-*3 b) ≡ (bin→nat (D1 , b)) * 3
bin-*3≡*3 {B1} = refl
bin-*3≡*3 {B D1 b} =
  bin→nat (D1 , bin-*3 (B D1 b))                       ≡⟨ refl ⟩
  bin→nat (D1 , bin-add (B D1 b) (B D0 (B D1 b)))      ≡⟨ bin-add≡+ (D1 , B D1 b) (D1 , (B D0 (B D1 b))) ⟩
  bin→nat (D1 , B D1 b) + bin→nat (D1 , B D0 (B D1 b)) ≡⟨ refl ⟩
  (2 * nb + 1) + 2 * (2 * nb + 1)                      ≡⟨ lemma (2 * nb + 1) ⟩
  (2 * nb + 1) * 3                                     ≡⟨ refl ⟩
  bin→nat (D1 , B D1 b) * 3 ∎
  where
    nb = bin→nat (D1 , b)

    lemma : (x : Nat) → x + (2 * x) ≡ x * 3
    lemma x = nat!

bin-*3≡*3 {B D0 b} =
  bin→nat (D1 , bb) + (bin→nat (D1 , bb) + zero) ≡⟨ (λ i → bin→nat (D1 , bb) + (+-zeror (bin→nat (D1 , bb)) i)) ⟩
  bin→nat (D1 , bb) + bin→nat (D1 , bb)          ≡⟨ +-dist≡ (bin-add≡+ (D1 , b) (D1 , B D0 b)) ⟩
  nb + nb0 + (nb + nb0)                          ≡⟨ ((λ i → nb + (ap bin→nat (lemma b) i) + (nb + (ap bin→nat (lemma b) i)))) ⟩
  nb + nb2 + (nb + nb2)                          ≡⟨ ((λ i → nb + (bin-double≡*2 (D1 , b) i) + (nb + (bin-double≡*2 (D1 , b) i))) ) ⟩
  nb + (2 * nb) + (nb + (2 * nb))                ≡⟨ refl ⟩
  nb + (nb + (nb + 0)) + (nb + (nb + (nb + 0)))  ≡⟨ refl ⟩
  (3 * nb) + (3 * nb)                            ≡⟨ sym (+-zeror ((3 * nb) + (3 * nb))) ⟩
  (3 * nb) + (3 * nb) + 0                        ≡⟨ sym (+-associative (3 * nb) (3 * nb) 0) ⟩
  (3 * nb) + ((3 * nb) + 0)                      ≡⟨ refl ⟩
  2 * (3 * nb)                                   ≡⟨ ((λ i → 2 * (*-commutative 3 nb i))) ⟩
  2 * (nb * 3)                                   ≡⟨ ((λ i → sym (*-associative 2 nb 3) i)) ⟩
  (nb + (nb + zero)) * 3                         ∎

  where

  nb = bin→nat (D1 , b)
  nb0 = bin→nat (D1 , B D0 b)
  nb2 = bin→nat (bin-double (D1 , b))
  bb = bin-add b (B D0 b)

  lemma : (x : Bin D1) → (D1 , B D0 x) ≡ bin-double (D1 , x)
  lemma B1 = refl
  lemma (B _ _) = refl

collatz : Bin D1 → Bin D1
collatz (B1) = B D0 (B D0 B1)
collatz (B D0 b) = b
collatz (B D1 b) = bin-inc (bin-*3 (B D1 b))

-- To prove the conjecture I have
-- to get this function to terminate
--
-- To convince agda I'll need to again
-- translate the problem into something
-- that shrinks with every step
collatz-proof : Σ Digit Bin → Σ Digit Bin
collatz-proof (D0 , B0) = D0 , B0
collatz-proof (D1 , B1) = D1 , B1
collatz-proof (D1 , B x b) = {!!}
--  collatz-proof (D1 , collatz (B x b))
