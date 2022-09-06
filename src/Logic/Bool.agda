
{-# OPTIONS --cubical #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

module Logic.Bool where

import 1Lab.Prelude as 1Lab
open import 1Lab.Prelude hiding (Bool; true; false; _∧_; _∨_)
open import Data.Bool using (Bool)
import Data.Bool as Bool

open import Logic.Classical

bool-pre-logic : PreLogic Bool
bool-pre-logic .PreLogic.true = Bool.true
bool-pre-logic .PreLogic.false = Bool.false
bool-pre-logic .PreLogic._∧_ Bool.true Bool.true = Bool.true
bool-pre-logic .PreLogic._∧_ _ _ = Bool.false
bool-pre-logic .PreLogic._∨_ Bool.true _ = Bool.true
bool-pre-logic .PreLogic._∨_ _ Bool.true = Bool.true
bool-pre-logic .PreLogic._∨_ _ _ = Bool.false
bool-pre-logic .PreLogic.¬ Bool.false = Bool.true
bool-pre-logic .PreLogic.¬ Bool.true = Bool.false
(bool-pre-logic PreLogic.⇒ Bool.false) Bool.false = Bool.true
(bool-pre-logic PreLogic.⇒ Bool.false) Bool.true = Bool.true
(bool-pre-logic PreLogic.⇒ Bool.true) Bool.false = Bool.false
(bool-pre-logic PreLogic.⇒ Bool.true) Bool.true = Bool.true

bool-classical : Classical Bool
bool-classical .Classical.is-pre-logic = bool-pre-logic
bool-classical .Classical.excluded-middle Bool.false = refl
bool-classical .Classical.excluded-middle Bool.true = refl
bool-classical .Classical.non-contradiction Bool.false = refl
bool-classical .Classical.non-contradiction Bool.true = refl
bool-classical .Classical.∧-comm Bool.false Bool.false = refl
bool-classical .Classical.∧-comm Bool.false Bool.true = refl
bool-classical .Classical.∧-comm Bool.true Bool.false = refl
bool-classical .Classical.∧-comm Bool.true Bool.true = refl
bool-classical .Classical.∧-demorgan Bool.false Bool.false = refl
bool-classical .Classical.∧-demorgan Bool.false Bool.true = refl
bool-classical .Classical.∧-demorgan Bool.true Bool.false = refl
bool-classical .Classical.∧-demorgan Bool.true Bool.true = refl
bool-classical .Classical.∨-demorgan Bool.false Bool.false = refl
bool-classical .Classical.∨-demorgan Bool.false Bool.true = refl
bool-classical .Classical.∨-demorgan Bool.true Bool.false = refl
bool-classical .Classical.∨-demorgan Bool.true Bool.true = refl
