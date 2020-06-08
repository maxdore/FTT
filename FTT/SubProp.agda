{-# OPTIONS --rewriting #-}

module FTT.SubProp where

open import FTT.Prelude
open import FTT.Core


-- Tm (Γ , A , B) (subT (subT B ((π₁ id ∘ π₁ id) ↑ A)) (subExt id (◁ ▼)))
-- π₁subext : ∀ {Γ} → π₁ (id {{!!}}) ∘ π₁ (id {{!!}}) ≡ subExt ((π₁ (id {{!!}}) ∘ π₁ (id {{!!}})) ∘ π₁ (id {{!!}})) (π₂ (id {{!!}})) 
-- π₁subext = {!!}


-- argh : ∀{Γ i j} {A : Ty Γ i} {B : Ty (Γ , A) j} {t : Tm Γ {!!}}
--   → subt (subt t (π₁ (id {{!!}}))) (π₁ (id {{!!}}) ∘ π₁ (id {{!!}}))
--   ≡ subt (π₂ (id {{!!}})) (π₁ (id {Γ , A , B}))
-- argh = {!!}

postulate
-- lemma : ∀{Γ n} {A : Ty Γ n} {t : Tm Γ A} → id ≡ (π₁ id ∘ subExt id t)

  mmh : ∀{Γ n} {A : Ty Γ n} → Tm Γ A ≡ Tm (Γ , A) (subT A wk)

  subtwk : ∀{Γ n} {A : Ty Γ n} {t : Tm Γ A} → subt t wk ≡ coe mmh t

{-# REWRITE subtwk #-}


postulate
-- error message: (π₁ id ∘ subExt id n) != id
  hack1 : {Γ : Cxt} {n : Tm Γ ℕᶠ} → subExt id (sucᶠ n) ≡ (subExt (π₁ id) (sucᶠ vz) ∘ subExt id n)
{-# REWRITE hack1 #-}
