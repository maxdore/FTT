{-# OPTIONS --rewriting #-}

module FTT.Examples.Basic where

open import FTT.Base


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

⊤tt : Tm ⟨⟩ ℕᶠ
⊤tt = ⊤test $ ttᶠ


