{-# OPTIONS --rewriting #-}

module FTT.Examples.SST2 where

open import FTT.Base

gt : ∀{Γ} {n : Tm Γ ℕᶠ} → (i j : Tm Γ (Finᶠ n)) → Ty Γ 0
gt {Γ} {n} fzeroᶠ y = ⊥ᶠ
gt {Γ} {n} (fsucᶠ x) fzeroᶠ = ⊤ᶠ
gt {Γ} {n} (fsucᶠ x) (fsucᶠ y) = gt x y
gt {Γ} {n} _ _ = ⊥ᶠ -- can't happen, but we have to split on other data constructors


postulate
  lift : ∀{Γ} {t : Tm Γ ℕᶠ}
    → subT (Finᶠ (subt t (π₁ (id {Γ , Finᶠ t})))) (π₁ (id {Γ , Finᶠ t , Finᶠ (◁ t)})) ≡ subT (Finᶠ t) (π₁ id ∘ π₁ id)


is-increasing : ∀{Γ} {m n : Tm Γ ℕᶠ} → (Tm Γ (Πᶠc 0 (Finᶠ m) (Finᶠ n))) → Ty Γ 0
is-increasing {Γ} {m} {n} f = Πᶠ 0 (Finᶠ m)
                             (Πᶠ 0 (Finᶠ (◁ m))
                                    (Πᶠc 0 (gt (◁ ▼) ▼)
                                           (gt ((◁ (◁ f)) $ ◁ ▼) ((◁ (◁ f)) $ (coe (TmΓ≡ lift) ▼)))))

-- hom-sets of Δ₊
_⇒+_ : ∀ {Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ → Ty Γ 1
_⇒+_ {Γ} m n = Σᶠ 1 (Πᶠc 0 (Finᶠ m) (Finᶠ n)) (is-increasing {Γ , Πᶠc 0 (Finᶠ m) (Finᶠ n)} {◁ m} {◁ n} ▼)


-- composition
-- TODO




postulate
    ⊤¹ : ∀{Γ} → Ty Γ 1
    tt¹ : ∀{Γ} → Tm Γ ⊤¹

Sk : ∀{Γ} → (B : Ty Γ 1) → (n : Tm Γ ℕᶠ) → (i : Tm Γ ℕᶠ) → Ty Γ 1
F : ∀{Γ} → (B : Ty Γ 1) → (i : Tm Γ ℕᶠ) → Tm Γ (Sk B i (pred i)) → Ty Γ 1
η : ∀{Γ} → (B : Ty Γ 1) → (n : Tm Γ ℕᶠ) → (i : Tm Γ ℕᶠ) → Tm Γ B → Tm Γ (Sk B n i)

Sk {Γ} B zeroᶠ i = ⊤¹
Sk {Γ} B (sucᶠ n) i = Σᶠ 1 (Sk B (sucᶠ n) i) (Πᶠ 0 ((◁ i) ⇒+ (◁ n)) ?)
Sk {_} _ _ _ = ⊤¹

F {Γ} B i m = Σᶠ 1 B (Idᶠ (Sk (◀ B) (◁ i) (pred (◁ i))) (η (◀ B) (◁ i) (pred (◁ i)) ▼) {!!}) -- (◁ x))

η {Γ} B zeroᶠ i x = tt¹
η {Γ} B (sucᶠ n) i b = pair ({!!}) (λᶠ (pair (◁ b) (reflᶠ {a = η (◀ B) (◁ i) (pred (◁ i)) (◁ b)})))
η {_} _ (appᶠ _) _ _ = tt¹



