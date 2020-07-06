{-# OPTIONS --rewriting #-}

module FTT.Eliminators where

open import FTT.Prelude
open import FTT.Core
open import FTT.Lemmas

-- The J-rule requires some lemmas, hence we have put it here instead of in
-- Core.agda


postulate
  Id-ind : ∀ {Γ m n}
    → {A : Ty Γ m}
    → {C : Ty (Γ , A , subT A wk , Idᶠ (◀ (◀ A)) (◁ ▼) ▼) n}
    → (c : Tm (Γ , A) (subT C (subExt (subExt (subExt wk ▼) ▼) reflᶠ)))
    → (a b : Tm Γ A)
    → (p : Tm Γ (Idᶠ A a b))
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt (subExt (subExt id a) (coe (TmΓ≡ IdHackLemma) b)) (coe (TmΓ≡ IdHack) p)))
