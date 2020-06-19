{-# OPTIONS --rewriting #-}

module FTT.Eliminators where

open import FTT.Prelude
open import FTT.Core
open import FTT.Lemmas

postulate
  subtvzwk : ∀{Γ i}{A : Ty Γ i}{u : Tm Γ A} → (subt vz (id {Γ , A , subT A wk})) ≡ (π₂ id)
  wkwksubExtExt :  ∀{Γ i}{A : Ty Γ i} {A : Ty Γ i} {a b : Tm Γ A}
    → A ≡ (subT A ((π₁ id ∘ π₁ (id {Γ , A , (subT A wk)})) ∘ subExt (subExt id a) b))


{-# REWRITE subtvzwk #-}



-- Elimination principles
postulate

  split : ∀{Γ l i j n}
      {A : Ty Γ i}
      {B : Ty (Γ , A) j}
    → (C : Ty (Γ , (Σᶠ l A B)) n)
    → (g : Tm (Γ , A , subT B (subExt wk vz)) (subT C (subExt (wk ∘ wk) (pair (◁ ▼) ▼))))
    → (p : Tm Γ (Σᶠ l A B))
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id p))

  -- Id-ind : ∀ {Γ n}
  --   → (A : Ty Γ n)
  --   → (C : Ty (Γ , A , subT A wk , Idᶠ (vsT (vsT A)) (vs vz) vz) n)
  --   → (c : Tm (Γ , A) (subT C (subExt (subExt (subExt wk vz) vz) {!!})))
  --   → (a b : Tm Γ A)
  --   → (p : Tm Γ (Idᶠ A a b))
  --   ---------------------------------------------------------
  --   → Tm Γ (subT C (subExt (subExt (subExt id a) b) (coe (TmΓ≡ (cong (Idᶠ {!!} {!!}) {!!})) p)))


  -- Σ-ind : ∀ {Γ n l i j}
  --   → {A : Ty Γ i}
  --   → {B : Ty (Γ , A) j}
  --   → (C : Ty (Γ , Σᶠ l A B) n)
  --   → (g : Tm (Γ , A , B) (subT C (subExt (wk ∘ wk) (pair (◁ ▼) ▼))))
  --   → (p : Tm Γ (Σᶠ l A B))
  --   ---------------------------------------------------------
  --   → Tm Γ (subT C (subExt id p))


  -- A⁰-ind : ∀ {Γ n}
  --     {A : Ty Γ 0}
  --   → (C : Ty (Γ , A) n)
  --   → (c : Tm (Γ , A) C)
  --   → (a : Tm Γ A)
  --   ---------------------------------------------------------
  --   → Tm Γ (subT C (subExt id a))

  -- ⊤-ind : ∀ {Γ n}
  --   → (C : Ty (Γ , ⊤ᶠ) n)
  --   → (c : Tm Γ (subT C (subExt id ttᶠ)))
  --   → (a : Tm Γ ⊤ᶠ)
  --   ---------------------------------------------------------
  --     → Tm Γ (subT C (subExt id a))

  -- parametrized by substitution:
  -- ⊤-ind : ∀ {Γ Δ n} {δ : Tms Γ Δ}
  -- → (C : Ty (Δ , ⊤ᶠ) n)
  -- → (c : Tm Δ (subT C (subExt id ttᶠ)))
  -- → (a : Tm Δ ⊤ᶠ)
  -- ---------------------------------------------------------
  -- → Tm Γ (subT (subT C (δ ↑ ⊤ᶠ)) (subExt id (subt a δ)))


  -- ℕ-ind : ∀ {Γ n}
  --   → (C : Ty (Γ , ℕᶠ) n)
  --   → (c₀ : Tm Γ (subT C (subExt id zeroᶠ)))
  --   → (cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz))))
  --   → (n : Tm Γ ℕᶠ)
  --   ---------------------------------------------------------
  --   → Tm Γ (subT C (subExt id n))

  -- Σ-ind : ∀ {Γ n l i j}
  --   → (A : Ty Γ i)
  --   → (B : Ty (Γ , A) j)
  --   → (C : Ty (Γ , Σᶠ l A B) n)
  --   → (g : Tm (Γ , A , B) (subT C (subExt ((π₁ id) ∘ (π₁ id))
  --             (pair {Γ , A , B} {l} {i} {j} {◀ (◀ A)} {◀ (◀ B)} (◁ ▼) (subt ▼ (subExt id (◁ ▼)))))))
  --             -- (pair (◁ ▼) (subt ▼ (subExt id (◁ ▼)))))))
  --   → (p : Tm Γ (Σᶠ l A B))
  --   ---------------------------------------------------------
  --   → Tm Γ (subT C (subExt id p))


-- K :
