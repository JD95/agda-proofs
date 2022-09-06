{-# OPTIONS --cubical #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

module Logic.Classical where

open import 1Lab.Prelude hiding (Bool; true; false; _∧_; _∨_)

record PreLogic {l : Level} (A : Type l) : Type (lsuc l) where
  field
    true : A
    false : A
    _∧_ : A → A → A
    _∨_ : A → A → A
    ¬ : A → A
    _⇒_ : A → A → A

record FirstOrder {l : Level} (A : Type l) : Type (lsuc l) where
  field
    pre-logic : PreLogic A

  open PreLogic pre-logic

  field
    modus-ponens : (p q : A) → ((p ⇒ q) ∧ p) ⇒ q ≡ true

record Classical
    {l : Level}
    (A : Type l)
  : Type (lsuc l) where

  field
    is-pre-logic : PreLogic A

  open PreLogic is-pre-logic

  field
    excluded-middle : (p : A) → (p ∨ (¬ p)) ≡ true
    non-contradiction : (p : A) → ¬ (p ∧ (¬ p)) ≡ true
    -- entailment-monotonicity : ???
    ∧-comm : (p q : A) → p ∧ q ≡ q ∧ p
    ∧-demorgan : (p q : A) → ¬ (p ∧ q) ≡ ¬ p ∨ ¬ q
    ∨-demorgan : (p q : A) → ¬ (p ∨ q) ≡ ¬ p ∧ ¬ q
