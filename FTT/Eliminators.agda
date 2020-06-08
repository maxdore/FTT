{-# OPTIONS --rewriting #-}

module FTT.Eliminators where

open import FTT.Prelude
open import FTT.Core
open import FTT.SubProp


-- Elimination principles
postulate
  A⁰-ind : ∀ {Γ n}
      {A : Ty Γ 0}
    → (C : Ty (Γ , A) n)
    → (c : Tm (Γ , A) C)
    → (a : Tm Γ A)
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id a))

  ⊤-ind : ∀ {Γ n}
    → (C : Ty (Γ , ⊤ᶠ) n)
    → (c : Tm Γ (subT C (subExt id ttᶠ)))
    → (a : Tm Γ ⊤ᶠ)
    ---------------------------------------------------------
      → Tm Γ (subT C (subExt id a))

  ℕ-ind : ∀ {Γ n}
    → (C : Ty (Γ , ℕᶠ) n)
    → (c₀ : Tm Γ (subT C (subExt id zeroᶠ)))
    → (cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz))))
    → (n : Tm Γ ℕᶠ)
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id n))

  Σ-ind : ∀ {Γ n l i j}
    → (A : Ty Γ i)
    → (B : Ty (Γ , A) j)
    → (C : Ty (Γ , Σᶠ l A B) n)
    -- → (g : Tm (Γ , A , B) (subT C (subExt ((π₁ id) ∘ (π₁ id))
    --           (pair {Γ , A , B} {l} {i} {j} {◀ (◀ A)} {◀ (◀ B)} (◁ ▼) (subt ▼ (subExt id (◁ ▼)))))))
    → (p : Tm Γ (Σᶠ l A B))
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id p))
    -- → Tm Γ (subT C (subExt id a))

  -- Id-ind : ∀ {Γ n}
  --   → (A : Ty Γ n)
  --   → (C : Ty (Γ , A , subT A wk , Idᶠ (vsT (vsT A)) (vs vz) vz) n)
  --   → (c : Tm (Γ , A) (subT (subT (subT C (subExt id {!vz!})) (subExt id {!!})) (subExt (π₁ id) {!!})))
  --   -- TODO replace third variable in C with refl!
  --   → (a b : Tm Γ A)
  --   → (p : Tm Γ (Idᶠ A a b))
  --   -- → (c₀ : Tm Γ (subT C (subExt id zeroᶠ)))
  --   -- → (cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz))))
  --   -- → (n : Tm Γ ℕᶠ)
  --   ---------------------------------------------------------
  --   → {!!}
    -- TODO replace third variable in C with p
    -- → Tm Γ (subT C (subExt id n))

-- K :
