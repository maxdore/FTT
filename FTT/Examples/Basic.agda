{-# OPTIONS --rewriting #-}

module FTT.Examples.Basic where

open import FTT.Base


-- TODO WHY DOESN'T IT WORK HERE???
-- appf : ∀{Γ l m n} {A : Ty Γ m} {B : Ty Γ n} → Tm Γ (Πᶠc {Γ} {m} {n} l A B) → Tm Γ A → Tm Γ B
-- appf f a = f $ a

-- exB : Ty (⟨⟩ , ⊤ᶠ , ⊥ᶠ) 0
-- exB = Πᶠ 0 (vsT (⊤-ind vz)) ℕᶠ

-- exC : Ty (⟨⟩ , ⊤ᶠ) 0
-- exC = ⊤-ind vz

pred : ∀{Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ
pred x = ℕ-ind ℕᶠ zeroᶠ ▼ x

+1 : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ ℕᶠ)
+1 {Γ}= λᶠ (ℕ-ind ℕᶠ (sucᶠ zeroᶠ) (sucᶠ vz) vz)

0+1 : Tm ⟨⟩ ℕᶠ
0+1 = +1 $ zeroᶠ

0+3 : Tm ⟨⟩ ℕᶠ
0+3 = +1 $ sucᶠ (sucᶠ (sucᶠ zeroᶠ))

⊤test : ∀{Γ} → Tm Γ (Πᶠ 0 ⊤ᶠ ℕᶠ)
⊤test = λᶠ (⊤-ind ℕᶠ zeroᶠ vz)
-- ⊤test = λᶠ (⊤-ind ℕᶠ {!!} {!!})

⊤tt : Tm ⟨⟩ ℕᶠ
⊤tt = ⊤test $ ttᶠ





-- Π (El (coe (TmΓ= U[]) vz)) U



-- get : ∀{Γ m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → Tm (Γ , A) B → Tm Γ A
-- get {Γ} {m} {n} {A} {B} x = {!!}

-- toℕ : {n : Tm ⟨⟩ ℕᶠ} → Tm ⟨⟩ (Finᶠ n) → Tm ⟨⟩ ℕᶠ
-- toℕ fzeroᶠ = zeroᶠ
-- toℕ (fsucᶠ x) = sucᶠ (toℕ x)

-- ℕᶠ→ℕ : Tm ⟨⟩ ℕᶠ → ℕ
-- ℕᶠ→ℕ zeroᶠ = zero
-- ℕᶠ→ℕ (sucᶠ x) = suc (ℕᶠ→ℕ x)

-- ℕ→ℕᶠ : ℕ → Tm ⟨⟩ ℕᶠ
-- ℕ→ℕᶠ zero = zeroᶠ
-- ℕ→ℕᶠ (suc x) = sucᶠ (ℕ→ℕᶠ x)

-- add' : Tm ⟨⟩ (ℕᶠ →ᶠ ℕᶠ)
-- add' = λᶠ (vs (add {!!}))
