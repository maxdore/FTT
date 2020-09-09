{-# OPTIONS --rewriting #-}

module FTT.Examples.Basic where

open import FTT.Base


pred : ∀{Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ
pred x = ℕ-ind ℕᶠ zeroᶠ ▼ x

+1 : ∀{Γ} → Tm Γ (Πᶠ ℕᶠ ℕᶠ)
+1 {Γ}= λᶠ (ℕ-ind ℕᶠ (sucᶠ zeroᶠ) (sucᶠ vz) vz)

0+1 : Tm ⟨⟩ ℕᶠ
0+1 = +1 $ zeroᶠ

0+3 : Tm ⟨⟩ ℕᶠ
0+3 = +1 $ sucᶠ (sucᶠ (sucᶠ zeroᶠ))

⊤test : ∀{Γ} → Tm Γ (Πᶠ ⊤ᶠ ℕᶠ)
⊤test = λᶠ (⊤-ind ℕᶠ zeroᶠ vz)

⊤tt : Tm ⟨⟩ ℕᶠ
⊤tt = ⊤test $ ttᶠ


lt : ∀{Γ} → Tm Γ (Πᶠ ℕᶠ (Πᶠ ℕᶠ (𝓤 0)))
lt {Γ} = λᶠ (ℕ-ind (Πᶠ ℕᶠ (𝓤 0))
                   (λᶠ (ℕ-ind (𝓤 0) (enc ⊥ᶠ) (enc ⊤ᶠ) ▼))
                   (λᶠ (enc (Σᶠ ⊤ᶠ ⊤ᶠ)))
                   ▼)

lttest : Tm ⟨⟩ (𝓤 0)
lttest = (lt $ zeroᶠ) $ sucᶠ zeroᶠ


Ω : ∀ {Γ n} → (A : Ty Γ n) → Tm Γ A → Ty Γ n
Ω A a = dec (pair {!pair!})
