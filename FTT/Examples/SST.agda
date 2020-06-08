{-# OPTIONS --rewriting #-}

module FTT.Examples.SST where

open import FTT.Base

-- Kraus' approach, c.f.
-- https://github.com/nicolaikraus/HoTT-Agda/blob/master/nicolai/SemiSimp/SStypes.agda

-- Can we explicitly define finite types?
-- postulate
--   Fin : ∀{Γ} → Tm Γ ℕᶠ → Ty Γ 1
--   fzero : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ (Fin (sucᶠ ▼)))
--   fsucc : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ (Πᶠ 0 (Finᶠ ▼) (Finᶠ (sucᶠ (◁ ▼)))))

-- gt : ∀{Γ} → Ty (Γ , ℕᶠ , Finᶠ ▼ , Finᶠ (◁ ▼) , ℕᶠ) 0
-- gt = Πᶠ 0 {!▼!} {!!}

-- DO WE NEED A MFUCKING UNIVERSE??!?!?!!?!???!?
-- gt : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ (Πᶠc 0 (Finᶠ ▼) (Finᶠ ▼))) → Ty Γ 0
-- gt f = {!!}

-- Cheat...
-- Fin : Tm ⟨⟩ ℕᶠ → Ty ⟨⟩ 1
-- Fin zeroᶠ = {!!}
-- Fin (sucᶠ x) = {!!}
-- fz : {n : ℕ} → Fin (S n)
-- fs : {n : ℕ} → Fin n → Fin (S n)

gt : ∀{Γ} {n : Tm Γ ℕᶠ} → (i j : Tm Γ (Finᶠ n)) → Ty Γ 0
gt {Γ} {n} fzeroᶠ y = ⊥ᶠ
gt {Γ} {n} (fsucᶠ x) fzeroᶠ = ⊤ᶠ
gt {Γ} {n} (fsucᶠ x) (fsucᶠ y) = gt x y
gt {Γ} {n} _ _ = ⊥ᶠ -- can't happen, but we have to split on other data constructors




is-increasing : ∀{Γ} {m n : Tm Γ ℕᶠ} → (Tm Γ (Πᶠc 0 (Finᶠ m) (Finᶠ n))) → Ty Γ 0
-- is-increasing {m} {n} f = {!!}
is-increasing {Γ} {m} {n} f = Πᶠ 0 (Finᶠ m)
                             (Πᶠ 0 (Finᶠ (◁ m))
                                    (Πᶠc 0 (gt (◁ ▼) ▼)
                                           (gt ((◁ (◁ f)) $ ◁ ▼) ((◁ (◁ f)) $ {!!}))))



is-increasing' : ∀{Γ} → {m n : Tm Γ ℕᶠ} → (Tm (Γ , ℕᶠ , ℕᶠ) (Πᶠc 0 (Finᶠ (◁ ▼)) (Finᶠ ▼))) → Ty Γ 0
is-increasing' {Γ} {m} {n} f = Πᶠ 0 (Finᶠ m)
                              (Πᶠ 0 (Finᶠ (◁ m))
                                (Πᶠc 0 (gt (◁ ▼) ▼)
                                       (gt ((◁ (◁ (subt f (subExt (subExt id m) n)))) $ ? ) -- ◁ ▼)
                                           ((◁ (◁ (subt f (subExt (subExt id m) n)))) $ {!!})
                                       )))



-- hom-sets of Δ₊
_⇒+_ : ∀ {Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ → Ty Γ 1
-- _⇒+_ {Γ} m n = Σᶠ 1 (Πᶠc 0 (Finᶠ m) (Finᶠ n)) (is-increasing {Γ , Πᶠc 0 (Finᶠ m) (Finᶠ n)} {◁ m} {◁ n} ▼)
_⇒+_ {Γ} m n = Σᶠ 1 (Πᶠc 0 (Finᶠ m) (Finᶠ n)) (is-increasing' {{!!}} {{!!}} {{!!}} ({!!} (◁ ▼)))


-- composition:
_∘+_ : {l : Tm ⟨⟩ ℕᶠ} → {m : Tm ⟨⟩ ℕᶠ} → {n : Tm ⟨⟩ ℕᶠ} → (Tm ⟨⟩ (m ⇒+ n)) → (Tm ⟨⟩ (l ⇒+ m)) → (Tm ⟨⟩ (l ⇒+ n))
g ∘+ f = {!!}
-- (g , p₂) ∘+ (f , p₁) = (λ i → g(f(i))) , (λ p → p₂ (p₁ p))

-- Semi-simplicial type of dimension n
SST : (n : ℕ) → Ty ⟨⟩ n

-- Skeleton of cells lower than j
Sk : {j : ℕ} → (Tm ⟨⟩ (SST j)) → (k : ℕ) → Ty ⟨⟩ k

-- Monos from bigger to smaller skeletons of the same SST
-- Skm : {j : ℕ} → (X : Tm ⟨⟩ (SST j)) → {k₁ k₂ : Tm ⟨⟩ ℕᶠ} → (Tm ⟨⟩ (k₁ ⇒+ k₂)) → Tm ⟨⟩ (Sk {j = j} X k₂) → Sk {j = j} X k₁

-- Skm commutes with composition
-- Skm-∘ : {j : ℕ} → (X : SST j) → {k₁ k₂ k₃ : ℕ} → (f : k₁ ⇒+ k₂) → (g : k₂ ⇒+ k₃) → (x : Sk X k₃) → Skm X (g ∘+ f) x ≡ Skm X f (Skm X g x)

SST zero = ⊤ᶠ
SST (suc n) = {!!}

Sk = {!!}

-- Skm = ?

-- Skm-∘ = ?
