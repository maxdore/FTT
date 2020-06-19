{-# OPTIONS --rewriting #-}

module FTT.Examples.SSIT where

open import FTT.Base

-- postulate
--     B : ∀{Γ} → Ty Γ 1

-- SST : ℕ → Ty Γ 1

X₀ : ∀{Γ} → Ty Γ 1 → Ty Γ 1
X₀ B = B

X₁ : ∀{Γ} → Ty Γ 1 → Ty Γ 1
X₁ B = Σᶠ 1 B (Σᶠ 1 (◀ B) (Idᶠ (◀ (◀ B)) (◁ ▼) ▼))

X₂ : ∀{Γ} → Ty Γ 1 → Ty Γ 1
X₂ B = Σᶠ 1 B
      (Σᶠ 1 (◀ B)
      (Σᶠ 1 (◀ (◀ B))
          (Σᶠ 0 (Idᶠ (◀ (◀ (◀ B))) (◁ (◁ ▼)) (◁ ▼))
          (Σᶠ 0 (Idᶠ (◀ (◀ (◀ (◀ B)))) (◁ (◁ (◁ ▼))) (◁ ▼))
          (Σᶠ 0 (Idᶠ (◀ (◀ (◀ (◀ (◀ B))))) (◁ (◁ (◁ ▼))) (◁ (◁ ▼)))
              (Idᶠ (Idᶠ (◀ (◀ (◀ (◀ (◀ (◀ B)))))) {!!} {!!}) {!!} ▼))))))


-- (Idᶠ (◀ (◀ B)) (◁ ▼) ▼))
