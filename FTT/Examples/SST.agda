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


-- lift : ∀{Γ i j} {A : Ty Γ i} {B : Ty (Γ , A) j} {t : Tm Γ A}
postulate
  lift : ∀{Γ} {t : Tm Γ ℕᶠ}
    → subT (Finᶠ (subt t (π₁ (id {Γ , Finᶠ t})))) (π₁ (id {Γ , Finᶠ t , Finᶠ (◁ t)})) ≡ subT (Finᶠ t) (π₁ id ∘ π₁ id)
--     -- → subT (Finᶠ (◁ t)) wk ≡ subT (Finᶠ t) (π₁ id ∘ π₁ id)


is-increasing : ∀{Γ} {m n : Tm Γ ℕᶠ} → (Tm Γ (Πᶠc 0 (Finᶠ m) (Finᶠ n))) → Ty Γ 0
is-increasing {Γ} {m} {n} f = Πᶠ 0 (Finᶠ m)
                             (Πᶠ 0 (Finᶠ (◁ m))
                                    (Πᶠc 0 (gt (◁ ▼) ▼)
                                           (gt ((◁ (◁ f)) $ ◁ ▼) ((◁ (◁ f)) $ (coe (TmΓ≡ lift) ▼)))))



-- is-increasing' : ∀{Γ} → {m n : Tm Γ ℕᶠ} → (Tm (Γ , ℕᶠ , ℕᶠ) (Πᶠc 0 (Finᶠ (◁ ▼)) (Finᶠ ▼))) → Ty Γ 0
-- is-increasing' {Γ} {m} {n} f = Πᶠ 0 (Finᶠ m)
--                               (Πᶠ 0 (Finᶠ (◁ m))
--                                 (Πᶠc 0 (gt (◁ ▼) ▼)
--                                        (gt ((◁ (◁ (subt f (subExt (subExt id m) n)))) $ {!!}) -- ◁ ▼)
--                                            ({!!} $ ▼) -- ▼)
--                                        )))



-- hom-sets of Δ₊
_⇒+_ : ∀ {Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ → Ty Γ 1
_⇒+_ {Γ} m n = Σᶠ 1 (Πᶠc 0 (Finᶠ m) (Finᶠ n)) (is-increasing {Γ , Πᶠc 0 (Finᶠ m) (Finᶠ n)} {◁ m} {◁ n} ▼)
-- _⇒+_ {Γ} m n = Σᶠ 1 (Πᶠc 0 (Finᶠ m) (Finᶠ n)) (is-increasing' {{!!}} {{!!}} {{!!}} ({!!} (◁ ▼)))

postulate
   -- compHack : ∀{Γ} (l : Tm Γ ℕᶠ) → (m : Tm Γ ℕᶠ) → (n : Tm Γ ℕᶠ) → (g : Tm Γ (m ⇒+ n))
   --                  → subt (subt l (π₁ id)) (subExt id g) ≡ l
   subTExt : ∀{Γ i j} {A : Ty Γ i} {B : Ty Γ j} {t : Tm Γ B} → subT (◀ A) (subExt id t) ≡ A



-- composition:
_∘+_ : ∀{Γ} → {l : Tm Γ ℕᶠ} → {m : Tm Γ ℕᶠ} → {n : Tm Γ ℕᶠ} → (Tm Γ (m ⇒+ n)) → (Tm Γ (l ⇒+ m)) → (Tm Γ (l ⇒+ n))
_∘+_ {Γ} {l} {m} {n} g f = coe {!!} (coe (TmΓ≡ subTExt) (split (◀ (l ⇒+ n)) {!!} g)) -- (◀ (l ⇒+ n)) {!!} g
-- _∘+_ {Γ} l m n g f = split (coe (Ty≡ (cong (_,_ Γ) refl)) (◀ (l ⇒+ n))) {!!} {!!} -- (◀ (l ⇒+ n)) {!!} g
-- _∘+_ {Γ} l m n g f = split {!!} (split {!!} (pair (λᶠ ((◁ (◁ (◁ (◁ ▼)))) $ ((◁ (◁ ▼)) $ ▼))) {!!}) (◁ (◁ f))) g

-- (◁ (◁ (◁ (◁ ▼)))) $ ((◁ (◁ ▼)) $ ▼)

-- Internal version
-- _∘+_ : ∀{Γ} → Tm (Γ , ℕᶠ , ℕᶠ , ℕᶠ , (◁ (▼) ⇒+ ▼) , (◁ (◁ (◁ ▼)) ⇒+ ◁ (◁ ▼))) (◁ (◁ (◁ (◁ ▼))) ⇒+ ◁ (◁ ▼))
-- _∘+_ {Γ} = split {!!} {!!} (◁ ▼)

-- _∘+_ : ∀{Γ} {p q r : Tm Γ ℕᶠ} → (Tm Γ (q ⇒+ r)) → (Tm Γ (p ⇒+ q)) → (Tm Γ (p ⇒+ r))
-- _∘+_ {Γ} {p} {q} {r} (pair g i) (pair f j) = pair (λᶠ ((coe ? (◁ g)) $ ((◁ f) $ ▼))) (λᶠ ((◁ i) $ ((coe ? (◁ j)) $ ▼)))
-- _∘+_ {Γ} {p} {q} {r} (pair g i) (pair f j) = pair (λᶠ ((◁ ?) $ ((◁ f) $ ▼))) (λᶠ ((◁ i) $ ((◁ ?) $ ▼)))
-- _∘+_ {Γ} {p} {q} {r} _ _ = {!!}
-- (g , p₂) ∘+ (f , p₁) = (λ i → g(f(i))) , (λ p → p₂ (p₁ p))

-- Semi-simplicial type of dimension n
SST : ∀{Γ} → Tm Γ ℕᶠ → Ty Γ 1

-- Skeleton of cells lower than j
Sk : ∀{Γ} {j : Tm Γ ℕᶠ} → (Tm Γ (SST j)) → Tm Γ ℕᶠ → Ty Γ 1

-- Monos from bigger to smaller skeletons of the same SST
Skm : ∀{Γ} {j : Tm Γ ℕᶠ} → (X : Tm Γ (SST j)) → {k₁ k₂ : Tm Γ ℕᶠ}
    → (Tm Γ (k₁ ⇒+ k₂)) → Tm Γ (Sk {j = j} X k₂) → Tm Γ (Sk {j = j} X k₁)

-- Skm commutes with composition

Skm-∘ : ∀{Γ} → {j : Tm Γ ℕᶠ} → (X : Tm Γ (SST j)) → {k₁ k₂ k₃ : Tm Γ ℕᶠ}
    → (f : Tm Γ (k₁ ⇒+ k₂)) → (g : Tm Γ (k₂ ⇒+ k₃)) → (Y : Tm Γ (Sk X k₃))
    → Tm Γ (Idᶠ (Sk X k₁) (Skm X (g ∘+ f) Y) (Skm X f (Skm X g Y)))

-- Skm-∘-coh : {j : ℕ} → (X : SST j) → {k₀ k₁ k₂ k₃ : ℕ} → (h : k₀ ⇒+ k₁) → (f : k₁ ⇒+ k₂) → (g : k₂ ⇒+ k₃) → (x : Sk X k₃)
--   → (Skm-∘ X h (g ∘+ f) x) ∙ (cong (Skm X h) (Skm-∘ X f g x)) ≡ (Skm-∘ X (f ∘+ h) g x) ∙ (Skm-∘ X h f (Skm X g x))

postulate
    SSTsubT : ∀{Γ n} → (subT (SST n) id) ≡ (SST n)

postulate
    ⊤¹ : ∀{Γ} → Ty Γ 1
    tt¹ : ∀{Γ} → Tm Γ ⊤¹

SST zeroᶠ = ⊤¹
-- SST (suc n) = Σᶠ (suc n) (SST n) (Πᶠ 0 (Sk (coe (TmΓ≡ SSTsubT) ▼) n) {!!}) -- Σ (SST j) λ X → Sk X j → Set
SST (sucᶠ n) = Σᶠ 1 (SST n) (Πᶠ 0 (Sk (coe (TmΓ≡ SSTsubT) ▼) (◁ n)) ?)
SST _ = ⊤¹

Sk = {!!}

Skm = {!!}

Skm-∘ = {!!}
