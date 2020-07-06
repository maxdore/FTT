{-# OPTIONS --rewriting #-}

module FTT.Examples.AdmissibleRules where

open import FTT.Base

-- This file explores some corollaries of Axiom L.


Ltest : ∀{Γ} → Tm Γ (Πᶠ 0 ⊤ᶠ ℕᶠ)
Ltest = λᶠ (L ℕᶠ ttᶠ zeroᶠ ttᶠ)

Ltest2 : ∀{Γ} → Tm Γ (Πᶠ 0 (Πᶠ 0 ℕᶠ ℕᶠ) (Πᶠ 0 ℕᶠ ℕᶠ))
Ltest2 = λᶠ (L ((Πᶠ 0 ℕᶠ ℕᶠ)) idf ▼ ▼)
  where
  idf : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ ℕᶠ)
  idf = λᶠ vz


-- The elimination principle for the unit type follows from Axiom L
⊤Elim : ∀{Γ n}
  → (C : Ty (Γ , ⊤ᶠ) n)
  → (c : Tm Γ (subT C (subExt id ttᶠ)))
  → (a : Tm Γ ⊤ᶠ)
  -------------------------------------
  → (Tm Γ (subT C (subExt id a)))
⊤Elim C c a = L C ttᶠ c a


-- These postulates establish some structural equalities that should hold, but
-- are laborious to prove.
postulate
  UIPhack : ∀{Γ} → {A : Ty Γ 1} → {a b : Tm Γ A}
    → (subT (Idᶠ A a b) (π₁ (id {Γ , Idᶠ A a b}))) ≡ (Idᶠ (◀ A) (◁ a) (◁ b))
  UIPhack2 : ∀{Γ} → {A : Ty Γ 1} → {a b : Tm Γ A} → {p q : Tm Γ (Idᶠ A a b)}
    → Idᶠ (Idᶠ A a b) p q ≡ subT (Idᶠ (Idᶠ (◀ A) (◁ a) (◁ b)) (coe (TmΓ≡ UIPhack) (◁ p)) (coe (TmΓ≡ UIPhack) ▼)) (subExt id q)


-- Uniqueness of identity proofs for all 1-types
UIP : ∀{Γ} → (A : Ty Γ 1) → (a b : Tm Γ A) → (p q : Tm Γ (Idᶠ A a b)) → (Tm Γ (Idᶠ (Idᶠ A a b) p q))
UIP {Γ} A a b p q = coe (TmΓ≡ (UIPhack2 ⁻¹)) (L {A = Idᶠ A a b}
                          (Idᶠ (Idᶠ (◀ A) (◁ a) (◁ b)) (coe (TmΓ≡ UIPhack) (◁ p)) (coe (TmΓ≡ UIPhack) ▼))
                          p
                          (coe (TmΓ≡ UIPhack2) (reflᶠ {A = Idᶠ A a b} {a = p}))
                          q)

