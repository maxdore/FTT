{-# OPTIONS --rewriting #-}

module FTT.Lemmas where

open import FTT.Prelude
open import FTT.Core

-- This file contains various lemmas for the structural rules. In a proper
-- implementation of FTT, all these should hold judgmentally. Due to time
-- reasons we have stated some of these as postulates.


id↑ : ∀{Γ n}{A : Ty Γ n} → id ↑ A ≡ id {Γ , A}
id↑ = refl

π₁= : ∀{Γ₀ Γ₁ n}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁}(Δ₂ : Δ₀ ≡ Δ₁)
  {A₀ : Ty Δ₀ n}{A₁ : Ty Δ₁ n}(A₂ : A₀ ≡[ Ty≡ Δ₂ ]≡ A₁)
  {δ₀ : Tms Γ₀ (Δ₀ , A₀)}{δ₁ : Tms Γ₁ (Δ₁ , A₁)}(δ₂ : δ₀ ≡[ Tms≡ Γ₂ (,C= Δ₂ A₂) ]≡ δ₁)
  → π₁ δ₀ ≡[ Tms≡ Γ₂ Δ₂ ]≡ π₁ δ₁
π₁= refl refl refl refl = refl

π₁=' : ∀{Γ Δ n}{A : Ty Δ n}{δ₀ δ₁ : Tms Γ (Δ , A)}(δ₂ : δ₀ ≡ δ₁) → π₁ δ₀ ≡ π₁ δ₁
π₁=' δ₂ = π₁= refl refl refl δ₂


-- π₁∘ : ∀{Γ Δ Θ n}{A : Ty Δ n}{δ : Tms Γ (Δ , A)}{ρ : Tms Θ Γ}
--   → π₁ δ ∘ ρ ≡ π₁ (δ ∘ ρ)
-- π₁∘ {Γ}{Δ}{Θ}{n}{A}{δ}{ρ} = (π₁β {Θ} {Δ} {n} {A} {π₁ δ ∘ ρ} {_}) ⁻¹
--                         ◾ π₁=' (,∘ ⁻¹)
--                         ◾ π₁=' (cong (λ x → x ∘ ρ) πη)

-- π₁id∘ : ∀{Γ Δ n}{A : Ty Δ n}{ρ : Tms Γ (Δ , A)}
--   → π₁ id ∘ ρ ≡ π₁ ρ
-- π₁id∘ = π₁∘ ◾ π₁=' idl

postulate
  wk∘<> : ∀{Γ i}{A : Ty Γ i}{u : Tm Γ A} → (π₁ id) ∘ (subExt id u) ≡ id
-- wk∘<> = π₁id∘ ◾ π₁β

  -- necessary for refl in c in Id-ind
  subt◀wk : ∀{Γ i} {A : Ty Γ i} → (subt (π₂ id) (π₁ (id {Γ , A , subT A wk}))) ≡ (π₂ id)

  IdHackLemma : ∀ {Γ n} {A : Ty Γ n} {a : Tm Γ A}
     → A ≡ subT (subT A wk) (subExt id a)

  IdHack : ∀ {Γ n} {A : Ty Γ n} {a b : Tm Γ A}
     → Idᶠ A a b ≡ subT (Idᶠ (◀ (◀ A)) (◁ ▼) (π₂ (id {Γ , A , subT A wk}))) (subExt (subExt id a) (coe (TmΓ≡ IdHackLemma) b))

  natHack : {Γ : Cxt} {n : Tm Γ ℕᶠ} → subExt id (sucᶠ n) ≡ (subExt (π₁ id) (sucᶠ (π₂ id)) ∘ subExt id n)


{-# REWRITE wk∘<> #-}
{-# REWRITE subt◀wk #-}
{-# REWRITE natHack #-}

