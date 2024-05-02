module Bin where

open import 1Lab.Prelude
open import 1Lab.Type.Pi
open import Data.Nat.Properties
open import Data.Nat.Base
open import Data.Nat.Solver using (nat!)

data Digit : Type where
  -- Has a 1
  D1 : Digit
  -- Has no 1s
  D0 : Digit

-- Represents binary numbers
-- with the digits in reverse
data Bin : Digit → Type where
  B0 : Bin D0
  B1 : Bin D1
  -- Prevents leading zeros
  B : Digit → Bin D1 → Bin D1

bin-inc : {d : Digit} → Bin d → Bin D1
bin-inc B0 = B1
bin-inc B1 = B D0 B1
bin-inc (B D1 d) = B D0 (bin-inc d)
bin-inc (B D0 d) = B D1 d

bin-double : Σ Digit Bin → Σ Digit Bin
bin-double (.D0 , B0) = D0 , B0
bin-double (.D1 , B1) = D1 , B D0 B1
bin-double (.D1 , B x b) = D1 , B D0 (B x b)

bin→nat : Σ Digit Bin → Nat
bin→nat (_ , B0) = zero
bin→nat (_ , B1) = suc zero
bin→nat (_ , B D1 d) = 2 * (bin→nat (D1 , d)) + 1
bin→nat (_ , B D0 d) = 2 * (bin→nat (D1 , d))

nat→bin : Nat → Σ Digit Bin
nat→bin zero = D0 , B0
nat→bin (suc x) = D1 , bin-inc (nat→bin x .snd)

bin-inc-is-suc : (b : Σ Digit Bin) →
   bin→nat (D1 , bin-inc (b .snd)) ≡
   suc (bin→nat b)
bin-inc-is-suc (.D0 , B0) = refl
bin-inc-is-suc (.D1 , B1) = refl
bin-inc-is-suc (.D1 , B D1 b) =
  let
    rec = bin-inc-is-suc (D1 , b)
    rb = bin→nat (D1 , b)
    inc-b = bin→nat (D1 , bin-inc b)
  in
  inc-b + (inc-b + zero)       ≡⟨ (λ i → (rec i) + (rec i + zero)) ⟩
  suc rb + (suc rb + zero)     ≡⟨ (λ i → suc rb + (+-zeror (suc rb) i)) ⟩
  suc rb + suc rb              ≡⟨ refl ⟩
  suc rb + (1 + rb)            ≡⟨ ((λ i → suc rb + (+-commutative 1 rb i))) ⟩
  suc rb + (rb + 1)            ≡⟨ refl ⟩
  suc (rb + (rb + 1))          ≡⟨ (λ i → suc rb + (sym (+-zeror rb) i + 1)) ⟩
  suc (rb + ((rb + zero) + 1)) ≡⟨ (λ i → suc (+-associative rb (rb + zero) 1 i)) ⟩
  suc (rb + (rb + zero) + 1) ∎

bin-inc-is-suc (.D1 , B D0 b) =
  let rb = bin→nat (D1 , b) in
  (rb + (rb + zero)) + 1 ≡⟨ sym (+-associative rb (rb + zero) 1) ⟩
  rb + ((rb + zero) + 1) ≡⟨ (λ i → rb + (+-commutative (rb + zero) 1 i)) ⟩
  rb + (1 + (rb + zero)) ≡⟨ +-associative rb 1 (rb + zero) ⟩
  (rb + 1) + (rb + zero) ≡⟨ ((λ i → (+-commutative rb 1 i) + (rb + zero))) ⟩
  (1 + rb) + (rb + zero) ≡⟨ refl ⟩
  suc (rb + (rb + zero)) ∎

bin≡nat : Σ Digit Bin ≡ Nat
bin≡nat = Iso→Path (bin→nat , iso nat→bin sect rect) where

   lemma2 : (x : Nat) →
     bin→nat (nat→bin (suc x)) ≡
     suc (bin→nat (nat→bin x))
   lemma2 zero = refl
   lemma2 (suc x) =
     let
       rec : bin→nat (nat→bin (suc x)) ≡
             suc (bin→nat (nat→bin x))
       rec = lemma2 x
     in
     bin→nat (nat→bin (suc (suc x)))               ≡⟨ refl ⟩
     bin→nat (D1 , bin-inc (nat→bin (suc x) .snd)) ≡⟨ bin-inc-is-suc (nat→bin (suc x)) ⟩
     suc (bin→nat (nat→bin (suc x))) ∎

   sect : (x : Nat) → bin→nat (nat→bin x) ≡ x
   sect zero = refl
   sect (suc x) =
     let rec = sect x in
     bin→nat (D1 , bin-inc (nat→bin x .snd)) ≡⟨ refl ⟩
     bin→nat (D1 , nat→bin (suc x) .snd)     ≡⟨ lemma2 x ⟩
     suc (bin→nat (nat→bin x))               ≡⟨ ((λ i → suc (rec i))) ⟩
     suc x ∎

   lemma5 : (b : Σ Digit Bin) →
     (D1 , bin-inc (bin-inc (bin-double b .snd))) ≡
     bin-double (D1 , bin-inc (b .snd))
   lemma5 (.D0 , B0) = refl
   lemma5 (.D1 , B1) = refl
   lemma5 (.D1 , B D1 b) = refl
   lemma5 (.D1 , B D0 b) = refl

   lemma4 : (x : Nat) → nat→bin (x + x) ≡ bin-double (nat→bin x)
   lemma4 zero = refl
   lemma4 (suc x) =
     let rec = lemma4 x in
     (D1 , bin-inc (nat→bin (x + suc x) .snd))              ≡⟨ (λ i → (D1 , bin-inc (nat→bin (+-commutative x (suc x) i) .snd))) ⟩
     (D1 , bin-inc (nat→bin (suc x + x) .snd))              ≡⟨ ((λ i → (D1 , bin-inc (bin-inc (rec i .snd))))) ⟩
     (D1 , bin-inc (bin-inc (bin-double (nat→bin x) .snd))) ≡⟨ lemma5 (nat→bin x) ⟩
     bin-double (D1 , bin-inc (nat→bin x .snd)) ∎

   lemma6 : (b : Bin D1) → bin-double (D1 , b) ≡ (D1 , B D0 b)
   lemma6 B1 = refl
   lemma6 (B x b) = refl

   rect : (x : Σ Digit Bin) → nat→bin (bin→nat x) ≡ x
   rect (D0 , B0) = refl
   rect (D1 , B1) = refl
   rect (D1 , B D1 b) =
     let
       rec = rect (D1 , b)
       rb = bin→nat (D1 , b)
     in
     nat→bin (rb + (rb + zero) + 1)                ≡⟨ (λ i → nat→bin (rb + (+-zeror rb i) + 1)) ⟩
     nat→bin (rb + rb + 1)                         ≡⟨ ((λ i → nat→bin (+-commutative (rb + rb) 1 i))) ⟩
     nat→bin (1 + (rb + rb))                       ≡⟨ refl ⟩
     (D1 , bin-inc (nat→bin (rb + rb) .snd))       ≡⟨ ((λ i → (D1 , bin-inc (lemma4 rb i .snd)))) ⟩
     (D1 , bin-inc (bin-double (nat→bin rb) .snd)) ≡⟨ (λ i → (D1 , bin-inc (bin-double (rec i) .snd))) ⟩
     (D1 , bin-inc (bin-double (D1 , b) .snd))     ≡⟨ (λ i → (D1 , bin-inc (lemma6 b i .snd))) ⟩
     (D1 , bin-inc (B D0 b))                       ≡⟨ refl ⟩
     (D1 , B D1 b) ∎

   rect (D1 , B D0 b) =
     let
       rb = bin→nat (D1 , b)
       rec = rect (D1 , b)
     in
     nat→bin (rb + (rb + zero)) ≡⟨ (λ i → nat→bin (rb + (+-zeror rb i))) ⟩
     nat→bin (rb + rb)          ≡⟨ lemma4 rb ⟩
     bin-double (nat→bin rb)    ≡⟨ ((λ i → bin-double (rec i))) ⟩
     bin-double (D1 , b)        ≡⟨ lemma6 b ⟩
     (D1 , B D0 b) ∎

carry : Digit → Digit → Digit
carry D1 D1 = D1
carry D1 D0 = D1
carry D0 D1 = D1
carry D0 D0 = D0

bin-add : {s t : Digit} → Bin s → Bin t → Bin (carry s t)
bin-add B0 B0 = B0
bin-add B0 B1 = B1
bin-add B0 (B x b) = B x b
bin-add B1 B0 = B1
bin-add B1 B1 = B D0 B1
bin-add B1 (B D1 b) = B D0 (bin-inc b)
bin-add B1 (B D0 b) = B D1 b
bin-add (B x y) B0 = B x y
bin-add (B x y) B1 = bin-inc (B x y)
bin-add (B D1 y) (B D1 z) = B D0 (bin-inc (bin-add y z))
bin-add (B D1 y) (B D0 z) = B D1 (bin-add y z)
bin-add (B D0 y) (B D1 z) = B D1 (bin-add y z)
bin-add (B D0 y) (B D0 z) = B D0 (bin-add y z)

bin-+ : Σ Digit Bin → Σ Digit Bin → Σ Digit Bin
bin-+ (D1 , x) (D1 , y) = D1 , bin-add x y
bin-+ (D1 , x) (D0 , y) = D1 , bin-add x y
bin-+ (D0 , x) (D1 , y) = D1 , bin-add x y
bin-+ (D0 , x) (D0 , y) = D0 , bin-add x y

bin→nat-inc : (y z : Bin D1) →
  bin→nat (D1 , bin-inc (bin-add y z)) ≡
  (1 + bin→nat (D1 , bin-add y z))
bin→nat-inc y z i = bin-inc-is-suc (D1 , bin-add y z) i

+-dist≡ : {x y : Nat} → (x≡y : x ≡ y) → x + x ≡ y + y
+-dist≡ x≡y i = (x≡y i) + (x≡y i)

bin-add-carry≡ : (y z : Bin D1) →
  (rec : bin→nat (bin-+ (D1 , y) (D1 , z)) ≡ bin→nat (D1 , y) + bin→nat (D1 , z)) →
  bin→nat (D1 , bin-add y z) + (bin→nat (D1 , bin-add y z) + zero) ≡
  bin→nat (D1 , y) + (bin→nat (D1 , y) + zero) + (bin→nat (D1 , z) + (bin→nat (D1 , z) + zero))
bin-add-carry≡ y z rec =
  let
    b1 = bin→nat (D1 , bin-add y z)
    ny = bin→nat (D1 , y)
    nz = bin→nat (D1 , z)
  in
  b1 + (b1 + zero)                      ≡⟨ (λ i → b1 + (+-zeror b1 i)) ⟩
  b1 + b1                               ≡⟨ (λ i → rec i + rec i) ⟩
  (ny + nz) + (ny + nz)                 ≡⟨ lemma ny nz ⟩
  ny + ny + (nz + nz)                   ≡⟨ ((λ i → ny + (sym (+-zeror ny) i) + (nz + sym (+-zeror nz) i))) ⟩
  ny + (ny + zero) + (nz + (nz + zero)) ∎
  where

  lemma : ∀ ny nz →
    (ny + nz) + (ny + nz) ≡
    ny + ny + (nz + nz)
  lemma ny nz = nat!

-- Need to make sure that my bin-add
-- function is correct
bin-add≡+ : (x y : Σ Digit Bin) →
  bin→nat (bin-+ x y) ≡
  bin→nat x + bin→nat y
-- Trivial cases
bin-add≡+ (_ , B0) (_ , B0) = refl
bin-add≡+ (_ , B0) (_ , B1) = refl
bin-add≡+ (_ , B0) (_ , B x y) = refl
bin-add≡+ (_ , B1) (_ , B0) = refl
bin-add≡+ (_ , B1) (_ , B1) = refl
bin-add≡+ (_ , B x y) (_ , B0) = sym (+-zeror _)
-- Harder Ones
bin-add≡+ (_ , B1) (_ , B D0 y) =
  let x = bin→nat (D1 , y) in
  (x + (x + zero)) + 1 ≡⟨ +-commutative (x + (x + zero)) 1 ⟩
  suc (x + (x + zero)) ∎

bin-add≡+ (_ , B1) (_ , B D1 y) =
  bin→nat (D1 , bin-add B1 (B D1 y)) ≡⟨ refl ⟩
  bin→nat (D1 , bin-inc (B D1 y))    ≡⟨ bin-inc-is-suc (D1 , B D1 y) ⟩
  suc (bin→nat (D1 , B D1 y)) ∎

bin-add≡+ (_ , B x y) (_ , B1) =
  bin→nat (D1 , bin-inc (B x y)) ≡⟨ bin-inc-is-suc (D1 , B x y) ⟩
  suc (bin→nat (D1 , B x y))     ≡⟨ refl ⟩
  1 + bin→nat (D1 , B x y)       ≡⟨ +-commutative 1 (bin→nat (D1 , B x y)) ⟩
  bin→nat (D1 , B x y) + 1 ∎

bin-add≡+ (_ , B D1 y) (_ , B D1 z) =
  let
    b1 = bin→nat (D1 , bin-inc (bin-add y z))
    b2 = bin→nat (D1 , bin-add y z)
    by+bz = bin-add≡+ (D1 , y) (D1 , z)
    ny = bin→nat (D1 , y)
    nz = bin→nat (D1 , z)
  in
  b1 + (b1 + zero)                              ≡⟨ (λ i → b1 + (+-zeror b1 i)) ⟩
  b1 + b1                                       ≡⟨ +-dist≡ (bin→nat-inc y z) ⟩
  (1 + b2) + (1 + b2)                           ≡⟨ +-dist≡ (λ i → (1 + by+bz i)) ⟩
  (1 + (ny + nz)) + (1 + (ny + nz))             ≡⟨ lemma ny nz ⟩
  ny + ny + 1 + (nz + nz + 1)                   ≡⟨ ((λ i → ny + (sym (+-zeror ny) i) + 1 + (nz + (sym (+-zeror nz) i) + 1))) ⟩
  ny + (ny + zero) + 1 + (nz + (nz + zero) + 1) ∎

  where

  lemma : ∀ x y →
    (1 + (x + y)) + (1 + (x + y)) ≡
    x + x + 1 + (y + y + 1)
  lemma x y = nat!

bin-add≡+ (_ , B D1 y) (_ , B D0 z) =
  lemma
    {b = bin→nat (D1 , y)}
    {d = bin→nat (D1 , z)}
    (bin-add-carry≡ y z (bin-add≡+ (D1 , y) (D1 , z)))

  where

  lemma2 : (b c d e : Nat) →
    (b + c + (d + e)) + 1 ≡
    b + c + 1 + (d +  e)
  lemma2 b c d e = nat!

  lemma :
    {a b c d e : Nat} →
    (a ≡ b + c + (d + e)) →
    (a + 1 ≡ b + c + 1 + (d + e))
  lemma {a} {b} {c} {d} {e} proof =
    a + 1                 ≡⟨ (λ i → proof i + 1) ⟩
    (b + c + (d + e)) + 1 ≡⟨ lemma2 b c d e ⟩
    b + c + 1 + (d +  e)  ∎

bin-add≡+ (_ , B D0 y) (_ , B D1 z) =
  lemma
    {b = bin→nat (D1 , y)}
    {d = bin→nat (D1 , z)}
    (bin-add-carry≡ y z (bin-add≡+ (D1 , y) (D1 , z)))

  where

  lemma2 : (b c d e : Nat) →
    (b + c + (d + e)) + 1 ≡
    b + c + (d +  e + 1)
  lemma2 b c d e = nat!

  lemma :
    {a b c d e : Nat} →
    (a ≡ b + c + (d + e)) →
    (a + 1 ≡ b + c + (d +  e + 1))
  lemma {a} {b} {c} {d} {e} proof =
    a + 1                 ≡⟨ (λ i → proof i + 1) ⟩
    (b + c + (d + e)) + 1 ≡⟨ lemma2 b c d e ⟩
    b + c + (d +  e + 1)  ∎

bin-add≡+ (_ , B D0 y) (_ , B D0 z) =
  bin-add-carry≡ y z (bin-add≡+ (D1 , y) (D1 , z))

bin-double≡*2 : (b : Σ Digit Bin) → bin→nat (bin-double b) ≡ 2 * bin→nat b
bin-double≡*2 (D0 , B0) = refl
bin-double≡*2 (D1 , B1) = refl
bin-double≡*2 (D1 , B D1 x) = refl
bin-double≡*2 (D1 , B D0 x) = refl
