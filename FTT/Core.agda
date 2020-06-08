{-# OPTIONS --rewriting #-}

module FTT.Core where

open import FTT.Prelude

{-# BUILTIN REWRITE _≡_ #-}

_≡[_]≡_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_


data Cxt : Set
data Ty : Cxt → ℕ → Set
data Tms : Cxt → Cxt → Set
data Tm : (Γ : Cxt) → {n : ℕ} → Ty Γ n → Set

data Cxt where
  ⟨⟩ : Cxt
  _,_ : (Γ : Cxt) → {n : ℕ} → Ty Γ n → Cxt

infixl 20 _,_

wk : {Γ : Cxt} {n : ℕ} {A : Ty Γ n} → Tms (Γ , A) Γ

data Ty where
  subT : {Γ Δ : Cxt} {n : ℕ} → Ty Δ n → Tms Γ Δ → Ty Γ n
  ⊥ᶠ : {Γ : Cxt} → Ty Γ 0
  ⊤ᶠ : {Γ : Cxt} → Ty Γ 0
  Πᶠ : {Γ : Cxt} {m n : ℕ} → (l : ℕ) → (A : Ty Γ m) → (B : (Ty (Γ , A) n)) → Ty Γ l
  Idᶠ : {Γ : Cxt} {n : ℕ} → (A : Ty Γ n) → (a b : Tm Γ A) → Ty Γ (predℕ n)
  -- Idᶠ : {Γ : Cxt} {n : ℕ} → (A : Ty Γ n) → Ty (Γ , A , subT A wk) (predℕ n)
  ℕᶠ : {Γ : Cxt} → Ty Γ 1
  Finᶠ : {Γ : Cxt} → Tm Γ ℕᶠ → Ty Γ 1
  Σᶠ : ∀{Γ m n} (l : ℕ) → (A : Ty Γ m) → (B : (Ty (Γ , A) n)) → Ty Γ l


-- Substitutions
data Tms where
  ε : {Γ : Cxt} → Tms Γ ⟨⟩
  subExt : {Γ Δ : Cxt} → {n : ℕ} → {A : Ty Δ n} → (δ : Tms Γ Δ) → Tm Γ (subT A δ) → Tms Γ (Δ , A)
  id : {Γ : Cxt} → Tms Γ Γ
  _∘_ : {Γ Δ Σ : Cxt} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  π₁ : {Γ Δ : Cxt} → {n : ℕ} → {A : Ty Δ n} → Tms Γ (Δ , A) → Tms Γ Δ



postulate
  [id]T : {Γ : Cxt} {n : ℕ} {A : Ty Γ n} → subT A id ≡ A
  [][]T : {Γ Δ Σ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ Δ} {σ : Tms Σ Γ} → subT (subT A δ) σ ≡ subT A (δ ∘ σ)



{-# REWRITE [id]T #-}
{-# REWRITE [][]T #-}


data Tm where
  -- Structural terms
  subt : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} → Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (subT A δ)
  π₂ : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} → (δ : Tms Γ (Δ , A)) → Tm Γ (subT A (π₁ δ))
  -- Introduction rules
  appᶠ : {Γ : Cxt} {l m n : ℕ} → {A : Ty Γ m} → {B : (Ty (Γ , A) n)} → Tm Γ (Πᶠ l A B) → Tm (Γ , A) B
  λᶠ : {Γ : Cxt} {l m n : ℕ} → {A : Ty Γ m} → {B : (Ty (Γ , A) n)} → Tm (Γ , A) B → Tm Γ (Πᶠ l A B)
  ttᶠ : {Γ : Cxt} → Tm Γ ⊤ᶠ
  zeroᶠ : {Γ : Cxt} → Tm Γ ℕᶠ
  sucᶠ : {Γ : Cxt} → Tm Γ ℕᶠ → Tm Γ ℕᶠ
  fzeroᶠ : {Γ : Cxt} → {n : Tm Γ ℕᶠ} → Tm Γ (Finᶠ (sucᶠ n))
  fsucᶠ : {Γ : Cxt} {n : Tm Γ ℕᶠ} → Tm Γ (Finᶠ n) → Tm Γ (Finᶠ (sucᶠ n))
  unpair : ∀{Γ l m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → Tm Γ (Σᶠ l A B) → Tm (Γ , A) B
  pair  : ∀{Γ l m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → (a : Tm Γ A) → Tm Γ (subT B (subExt id a)) → Tm Γ (Σᶠ l A B)
  -- Euality types
  -- reflᶠ    : ∀{Γ n} {A : Ty Γ n} → Tm (Γ , A , subT A wk) (Idᶠ A)
  reflᶠ : {Γ : Cxt} {n : ℕ} → (A : Ty Γ n) → (a : Tm Γ A) → Tm Γ (Idᶠ A a a)
  -- • TODO!!!


wk = π₁ id

vz : {Γ : Cxt} {n : ℕ} {A : Ty Γ n} → Tm (Γ , A) (subT A wk)
vz = π₂ id

vs : {Γ : Cxt} {m n : ℕ} {A : Ty Γ m} {B : Ty Γ n} → Tm Γ A → Tm (Γ , B) (subT A wk)
vs x = subt x wk

vsT : ∀{Γ m n} {A : Ty Γ m} → Ty Γ n → Ty (Γ , A) n
vsT B = subT B wk


▼ = vz
◁ = vs
◀ = vsT


Ty≡ : {Γ₀ Γ₁ : Cxt}{n : ℕ }(Γ₂ : Γ₀ ≡ Γ₁) → Ty Γ₀ n ≡ Ty Γ₁ n
Ty≡ refl = refl

Tms≡ : {Γ₀ Γ₁ : Cxt}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁ : Cxt}(Δ₂ : Δ₀ ≡ Δ₁) → Tms Γ₀ Δ₀ ≡ Tms Γ₁ Δ₁
Tms≡ refl refl = refl

TmΓ≡ : {Γ : Cxt} {n : ℕ} {A B : Ty Γ n} → (A ≡ B) → Tm Γ A ≡ Tm Γ B
TmΓ≡ {Γ} p = cong (Tm Γ) p

,C= : {Γ₀ Γ₁ : Cxt}{n : ℕ}(Γ₂ : Γ₀ ≡ Γ₁){A₀ : Ty Γ₀ n}{A₁ : Ty Γ₁ n}(A₂ : A₀ ≡[ Ty≡ Γ₂ ]≡ A₁)
  → _≡_ {A = Cxt} (Γ₀ , A₀) (Γ₁ , A₁)
,C= refl refl = refl


_↑_  : {Γ Δ : Cxt} {n : ℕ} → (δ : Tms Γ Δ)(A : Ty Δ n) → Tms (Γ , (subT A δ)) (Δ , A)
δ ↑ A = subExt (δ ∘ π₁ id) (π₂ id)
-- δ ↑ A = subExt (δ ∘ π₁ id) (coe (TmΓ≡ [][]T) (π₂ id))

postulate
  ⊤[] : {Γ Δ : Cxt} {δ : Tms Γ Δ} → subT ⊤ᶠ δ ≡ ⊤ᶠ
  Π[] : {Γ Δ : Cxt} {l m n : ℕ} {A : Ty Δ m} {B : Ty (Δ , A) n} {δ : Tms Γ Δ} → subT (Πᶠ l A B) δ ≡ Πᶠ l (subT A δ) (subT B (δ ↑ A))
  Σ[] : {Γ Δ : Cxt} {l m n : ℕ} {A : Ty Δ m} {B : Ty (Δ , A) n} {δ : Tms Γ Δ} → subT (Σᶠ l A B) δ ≡ Σᶠ l (subT A δ) (subT B (δ ↑ A))
  ℕ[] : {Γ Δ : Cxt} {δ : Tms Γ Δ} → subT ℕᶠ δ ≡ ℕᶠ

{-# REWRITE ⊤[] #-}
{-# REWRITE Π[] #-}
{-# REWRITE Σ[] #-}
{-# REWRITE ℕ[] #-}

postulate
  Fin[] : {Γ Δ : Cxt} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subT (Finᶠ n) δ ≡ Finᶠ (subt n δ)
  -- ⊤-ind[] : {Γ Δ : Cxt} {n : ℕ} {t  : Tm Δ ⊤ᶠ} {δ : Tms Γ Δ} → subT (⊤-ind t) δ ≡ ⊤-ind (subt t δ)
  -- ℕ-el[] : {Γ Δ : Cxt} {n : ℕ} {t  : Tm Δ ℕᶠ} {δ : Tms Γ Δ} → subT (ℕ-el t) δ ≡ ℕ-el (subt t δ)

{-# REWRITE Fin[] #-}
-- {-# REWRITE ⊤-ind[] #-}
-- {-# REWRITE ℕ-el[] #-}


postulate
  idl : {Γ Δ : Cxt} {δ : Tms Γ Δ} → id ∘ δ ≡ δ
  idr : {Γ Δ : Cxt} {δ : Tms Γ Δ} → δ ∘ id ≡ δ
  ass : {Γ Δ Σ Ω : Cxt} {δ : Tms Γ Δ} {σ : Tms Σ Γ} {ν : Tms Ω Σ} →
    (δ ∘ σ) ∘ ν ≡ δ ∘ (σ ∘ ν)
  ,∘ : {Γ Δ Σ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ Δ} {σ : Tms Σ Γ} {t : Tm Γ (subT A δ)} →
    (subExt δ t) ∘ σ ≡ subExt {Σ} {Δ} {n} {A} (δ ∘ σ) (coe (TmΓ≡ {Σ} {n} {subT (subT A δ) σ} {subT A (δ ∘ σ)} ([][]T {Γ} {Δ} {Σ} {n} {A} {δ} {σ})) (subt t σ))
  π₁β : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ Δ} {t : Tm Γ (subT A δ)} →
    π₁ {Γ} {Δ} {n} {A} (subExt δ t) ≡ δ
  πη  : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ (Δ , A)} →
    subExt (π₁ δ) (π₂ δ) ≡ δ
  -- π[]t  : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ (Δ , A)} →
  --   subt (π₂ δ) (π₁ id) ≡ subt {!!} {!δ!}
  εη  : {Γ : Cxt} {ε' : Tms Γ ⟨⟩} → ε' ≡ ε

{-# REWRITE idl #-}
{-# REWRITE idr #-}
{-# REWRITE ass #-}
{-# REWRITE ,∘ #-}
{-# REWRITE π₁β #-}
{-# REWRITE πη #-}
-- {-# REWRITE εη #-}
