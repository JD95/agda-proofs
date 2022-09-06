
{-# OPTIONS --cubical #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

module Logic.Types where

import 1Lab.Prelude as 1Lab
open import 1Lab.Prelude
open import Data.Sum

open import Logic.Classical

-- General types can only be a pre-logic
-- without parametricity things like modus-ponens
-- can't be proved
type-pre-logic : PreLogic Type
type-pre-logic .PreLogic.true = ⊤
type-pre-logic .PreLogic.false = ⊥
type-pre-logic .PreLogic._∧_ = _×_
type-pre-logic .PreLogic._∨_ = _⊎_
type-pre-logic .PreLogic.¬ x = x → ⊥
type-pre-logic .PreLogic._⇒_ x y = x → y

-- However, propositional types can form a logic
prop-pre-logic : {l : Level} → PreLogic (1Lab.Prop l)
prop-pre-logic {l} .PreLogic.true =
  Lift l ⊤  , λ x y → refl
prop-pre-logic {l} .PreLogic.false =
  Lift l ⊥ , λ ()
prop-pre-logic {l} .PreLogic._∧_ p q =
  (p .∣_∣ × q .∣_∣) , ×-is-hlevel 1 (p .is-tr) (q .is-tr)
prop-pre-logic {l} .PreLogic._∨_ p q =
  ∥ p .∣_∣ ⊎ q .∣_∣ ∥ , squash
prop-pre-logic {l} .PreLogic.¬ x =
  Lift l (x .∣_∣ → ⊥) , Lift-is-hlevel 1 (fun-is-hlevel 1 (hlevel 1))
prop-pre-logic {l} .PreLogic._⇒_ x y =
  Lift l (x .∣_∣ → y .∣_∣) , Lift-is-hlevel 1 (fun-is-hlevel 1 (y .is-tr))

prop-first-order : {l : Level} → FirstOrder (1Lab.Prop l)
prop-first-order .FirstOrder.pre-logic = prop-pre-logic
prop-first-order {l} .FirstOrder.modus-ponens p q i = lemma2 i , lemma3 i where

 Ap : Type l
 Ap = Lift l (Lift l (p .∣_∣ → q .∣_∣) × p .∣_∣ → q .∣_∣)

 Ap-prop : is-prop Ap
 Ap-prop = Lift-is-hlevel 1 (fun-is-hlevel 1 (q .is-tr))

 univ : Ap
 univ = lift (λ (lift f , x) → f x)

 ap-is-contr : is-contr Ap
 ap-is-contr = contr univ (Ap-prop univ)

 f : Ap → Lift l ⊤
 f _ = lift tt

 lemma : is-equiv f
 lemma = is-contr→is-equiv ap-is-contr (hlevel 0)

 lemma2 : Ap ≡ Lift l ⊤
 lemma2 = Iso→Path (f , is-equiv→is-iso lemma)

 lemma3 : PathP (λ i → is-prop (lemma2 i)) Ap-prop (hlevel 1)
 lemma3 = is-prop→pathp (λ i → is-prop-is-prop) Ap-prop (hlevel 1)
