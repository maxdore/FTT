{-# OPTIONS --rewriting #-}

module FTT.Examples.SSTint where

open import FTT.Base

-- Kraus' approach, c.f.
-- https://github.com/nicolaikraus/HoTT-Agda/blob/master/nicolai/SemiSimp/SStypes.agda

-- gt : ∀{Γ} → Ty (Γ , ℕᶠ , Finᶠ ▼ , Finᶠ (◁ ▼)) 0
-- gt {Γ} = dec {!!} -- needs Fin recursors

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


-- -- postulate
--    -- compHack : ∀{Γ} (l : Tm Γ ℕᶠ) → (m : Tm Γ ℕᶠ) → (n : Tm Γ ℕᶠ) → (g : Tm Γ (m ⇒+ n))
--    --                  → subt (subt l (π₁ id)) (subExt id g) ≡ l
--    -- subTExt : ∀{Γ i j} {A : Ty Γ i} {B : Ty Γ j} {t : Tm Γ B} → subT (◀ A) (subExt id t) ≡ A
--    -- compHack : ∀{Γ} (n : Tm Γ ℕᶠ) → (m : Tm Γ ℕᶠ) → (g : Tm Γ (m ⇒+ n))
--    --   → subt (subt n (π₁ id)) (subExt (π₁ (id {?}) ∘ π₁ (id {?})) (π₂ id)) ≡ n

-- -- composition:
_∘+_ : ∀{Γ} → {l : Tm Γ ℕᶠ} → {m : Tm Γ ℕᶠ} → {n : Tm Γ ℕᶠ}
  → (Tm Γ (m ⇒+ n)) → (Tm Γ (l ⇒+ m)) → (Tm Γ (l ⇒+ n))
_∘+_ {Γ} {l} {m} {n} g f = {!!}

-- Semi-simplicial type of dimension n
SST : ∀{Γ} → Ty (Γ , ℕᶠ) 1
-- EXT SST : ∀{Γ} → Tm Γ ℕᶠ → Ty Γ 1

-- Skeleton of cells lower than j
Sk : ∀{Γ} → Ty (Γ , ℕᶠ , SST , ℕᶠ) 1
-- EXT Sk : ∀{Γ} {n : Tm Γ ℕᶠ} → (Tm Γ (SST n)) → Tm Γ ℕᶠ → Ty Γ 1

-- Monos from bigger to smaller skeletons of the same SST
-- Skm : ∀{Γ} {n : Tm Γ ℕᶠ} → (X : Tm Γ (SST n)) → {k₁ k₂ : Tm Γ ℕᶠ}
--     → (Tm Γ (k₁ ⇒+ k₂)) → Tm Γ (Sk {n = n} X k₂) → Tm Γ (Sk {n = n} X k₁)

-- Skm commutes with composition

-- Skm-∘ : ∀{Γ} → {j : Tm Γ ℕᶠ} → (X : Tm Γ (SST j)) → {k₁ k₂ k₃ : Tm Γ ℕᶠ}
--     → (f : Tm Γ (k₁ ⇒+ k₂)) → (g : Tm Γ (k₂ ⇒+ k₃)) → (Y : Tm Γ (Sk X k₃))
--     → Tm Γ (Idᶠ (Sk X k₁) (Skm X (g ∘+ f) Y) (Skm X f (Skm X g Y)))

-- Skm-∘-coh : {j : ℕ} → (X : SST j) → {k₀ k₁ k₂ k₃ : ℕ} → (h : k₀ ⇒+ k₁) → (f : k₁ ⇒+ k₂) → (g : k₂ ⇒+ k₃) → (x : Sk X k₃)
--   → (Skm-∘ X h (g ∘+ f) x) ∙ (cong (Skm X h) (Skm-∘ X f g x)) ≡ (Skm-∘ X (f ∘+ h) g x) ∙ (Skm-∘ X h f (Skm X g x))

-- postulate
--     SSTsubT : ∀{Γ n} → (subT (SST n) id) ≡ (SST n)

postulate
    ⊤¹ : ∀{Γ} → Ty Γ 1
    tt¹ : ∀{Γ} → Tm Γ ⊤¹

{-# TERMINATING #-}
SST {Γ} = dec (ℕ-ind (𝓤 1)
                     (enc ⊤¹)
                     (enc (Σᶠ 1 SST (Πᶠ 0 {!Sk!} (𝓤 1))))
                     ▼)


Sk {Γ} = dec (ℕ-ind (𝓤 1)
                    (enc ⊤¹)
                    (enc (Σᶠ 1 {!!} (Πᶠ 0 ({!!} ⇒+ {!!}) {!_$_!})))
                    (◁ (◁ ▼)))
