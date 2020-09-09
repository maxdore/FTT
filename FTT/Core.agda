{-# OPTIONS --rewriting #-}

module FTT.Core where

open import FTT.Prelude

𝔻 = ℕ
pred𝔻 = predℕ
suc𝔻 = suc
sup𝔻 = supℕ

data Cxt : Set
data Ty : Cxt → 𝔻 → Set
data Tms : Cxt → Cxt → Set
data Tm : (Γ : Cxt) → {n : 𝔻} → Ty Γ n → Set

data Cxt where
  ⟨⟩ : Cxt
  _,_ : (Γ : Cxt) → {n : 𝔻} → Ty Γ n → Cxt

infixl 20 _,_

-- Type formers
data Ty where
  subT : {Γ Δ : Cxt} {n : 𝔻} → Ty Δ n → Tms Γ Δ → Ty Γ n
  ⊥ᶠ : {Γ : Cxt} → Ty Γ 0
  ⊤ᶠ : {Γ : Cxt} → Ty Γ 0
  Πᶠ : ∀{Γ m n} → (A : Ty Γ m) → (B : (Ty (Γ , A) n)) → Ty Γ n
  Σᶠ : ∀{Γ m n} → (A : Ty Γ m) → (B : (Ty (Γ , A) n)) → Ty Γ (sup𝔻 m n)
  Idᶠ : {Γ : Cxt} {n : 𝔻} → (A : Ty Γ n) → (a b : Tm Γ A) → Ty Γ (pred𝔻 n)
  ℕᶠ : {Γ : Cxt} → Ty Γ 1
  Finᶠ : {Γ : Cxt} → Tm Γ ℕᶠ → Ty Γ 1
  cumT : ∀{Γ n} → Ty Γ n → Ty Γ (suc𝔻 n)
  𝓤 : ∀{Γ} → (n : 𝔻) → Ty Γ (suc𝔻 n)
  -- HITs
  MSet : {Γ : Cxt} → Ty Γ 1 → Ty Γ 1


-- Substitutions
data Tms where
  ε : {Γ : Cxt} → Tms Γ ⟨⟩
  subExt : {Γ Δ : Cxt} → {n : 𝔻} → {A : Ty Δ n} → (δ : Tms Γ Δ) → Tm Γ (subT A δ) → Tms Γ (Δ , A)
  id : {Γ : Cxt} → Tms Γ Γ
  _∘_ : {Γ Δ Σ : Cxt} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  π₁ : {Γ Δ : Cxt} → {n : 𝔻} → {A : Ty Δ n} → Tms Γ (Δ , A) → Tms Γ Δ


_⇒_ : Cxt → Cxt → Set
_⇒_ = Tms


postulate
  [id]T : ∀{Γ n} {A : Ty Γ n} → subT A id ≡ A
  [][]T : ∀ {Γ Δ Σ n} {A : Ty Δ n} {δ : Γ ⇒ Δ} {σ : Σ ⇒ Γ}
      → subT (subT A δ) σ ≡ subT A (δ ∘ σ)

{-# REWRITE [id]T #-}
{-# REWRITE [][]T #-}

_↑_  : {Γ Δ : Cxt} {n : 𝔻} → (δ : Tms Γ Δ)(A : Ty Δ n) → Tms (Γ , (subT A δ)) (Δ , A)

postulate
  𝓤[] : {Γ Δ : Cxt} {n : 𝔻} {δ : Tms Γ Δ} → subT (𝓤 n) δ ≡ 𝓤 n
  Π[] : {Γ Δ : Cxt} {m n : 𝔻} {A : Ty Δ m} {B : Ty (Δ , A) n} {δ : Tms Γ Δ} → subT (Πᶠ A B) δ ≡ Πᶠ (subT A δ) (subT B (δ ↑ A))
  Σ[] : ∀{Γ Δ m n}{A : Ty Δ m} {B : Ty (Δ , A) n} {δ : Tms Γ Δ} → subT (Σᶠ A B) δ ≡ Σᶠ (subT A δ) (subT B (δ ↑ A))
  ⊤[] : ∀{Γ Δ} {δ : Γ ⇒ Δ} → subT ⊤ᶠ δ ≡ ⊤ᶠ
  ℕ[] : {Γ Δ : Cxt} {δ : Tms Γ Δ} → subT ℕᶠ δ ≡ ℕᶠ

{-# REWRITE 𝓤[] #-}
{-# REWRITE ⊤[] #-}
{-# REWRITE Π[] #-}
{-# REWRITE Σ[] #-}
{-# REWRITE ℕ[] #-}


wk : {Γ : Cxt} {n : 𝔻} {A : Ty Γ n} → Tms (Γ , A) Γ
vz : {Γ : Cxt} {n : 𝔻} {A : Ty Γ n} → Tm (Γ , A) (subT A wk)
vs : {Γ : Cxt} {m n : 𝔻} {A : Ty Γ m} {B : Ty Γ n} → Tm Γ A → Tm (Γ , B) (subT A wk)
vsT : ∀{Γ m n} {A : Ty Γ m} → Ty Γ n → Ty (Γ , A) n



data Tm where
  -- Structural terms
  subt : {Γ Δ : Cxt} {n : 𝔻} {A : Ty Δ n} → Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (subT A δ)
  π₂ : {Γ Δ : Cxt} {n : 𝔻} {A : Ty Δ n} → (δ : Tms Γ (Δ , A)) → Tm Γ (subT A (π₁ δ))

  -- lift term in universe
  cumt : ∀{Γ n} {A : Ty Γ n} → Tm Γ A → Tm Γ (cumT A)

  -- Axiom L
  L : ∀ {Γ n}
    {A : Ty Γ 0}
    → (C : Ty (Γ , A) n)
    → (a : Tm Γ A)
    → (c : Tm Γ (subT C (subExt id a)))
    → (b : Tm Γ A)
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id b))

  λᶠ : ∀ {Γ m n}
      {A : Ty Γ m}
      {B : (Ty (Γ , A) n)}
    → Tm (Γ , A) B
    ---------------------------------------------------------
    → Tm Γ (Πᶠ A B)

  appᶠ : ∀ {Γ m n}
    {A : Ty Γ m}
    {B : (Ty (Γ , A) n)}
    → Tm Γ (Πᶠ A B)
    ---------------------------------------------------------
    → Tm (Γ , A) B

  pair  : ∀{Γ m n}
      {A : Ty Γ m}
      {B : Ty (Γ , A) n}
    → (a : Tm Γ A)
    → Tm Γ (subT B (subExt id a))
    ---------------------------------------------------------
    → Tm Γ (Σᶠ A B)

  fst : ∀ {Γ m n}
    {A : Ty Γ m}
    {B : (Ty (Γ , A) n)}
    → Tm Γ (Σᶠ A B)
    ---------------------------------------------------------
    → Tm Γ A

  snd : ∀{Γ m n}
    {A : Ty Γ m}
    {B : (Ty (Γ , A) n)}
    → (t : Tm Γ (Σᶠ A B))
    ---------------------------------------------------------
    → Tm Γ (subT B (subExt id (fst t)))

  ttᶠ : {Γ : Cxt} → Tm Γ ⊤ᶠ
  zeroᶠ : {Γ : Cxt} → Tm Γ ℕᶠ
  sucᶠ : {Γ : Cxt} → Tm Γ ℕᶠ → Tm Γ ℕᶠ
  fzeroᶠ : {Γ : Cxt} → {n : Tm Γ ℕᶠ} → Tm Γ (Finᶠ (sucᶠ n))
  fsucᶠ : {Γ : Cxt} {n : Tm Γ ℕᶠ} → Tm Γ (Finᶠ n) → Tm Γ (Finᶠ (sucᶠ n))
  reflᶠ : {Γ : Cxt} {n : 𝔻} → {A : Ty Γ n} → {a : Tm Γ A} → Tm Γ (Idᶠ A a a)

  ⊤-ind : ∀ {Γ n} (C : Ty (Γ , ⊤ᶠ) n) (c : Tm Γ (subT C (subExt id ttᶠ))) (a : Tm Γ ⊤ᶠ) → Tm Γ (subT C (subExt id a))

  ℕ-ind : ∀ {Γ n}
    → (C : Ty (Γ , ℕᶠ) n)
    → (c₀ : Tm Γ (subT C (subExt id zeroᶠ)))
    → (cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz))))
    → (n : Tm Γ ℕᶠ)
    ---------------------------------------------------------
    → Tm Γ (subT C (subExt id n))

  -- HIT constructors
  -- []ᵐ : {Γ : Cxt} {A : Ty Γ 1} → Tm Γ (MSet A)
  -- ∷ᵐ : {Γ : Cxt} {A : Ty Γ 1} → Tm Γ A → Tm Γ (MSet A) → Tm Γ (MSet A)
  -- commᵐ : {Γ : Cxt} {A : Ty Γ 1} → (x : Tm Γ A) → (y : Tm Γ A) → (xs : Tm Γ (MSet A)) → Tm Γ (Idᶠ (MSet A) (∷ᵐ x (∷ᵐ y xs)) (∷ᵐ y (∷ᵐ x xs)))
  -- MSet-ind : ∀ {Γ n} {A : Ty Γ 1}
  --   → (C : Ty (Γ , MSet A) n)
  --   → (e : Tm Γ (subT C (subExt id []ᵐ)))
  --   → (cₛ : Tm (Γ , A , vsT (MSet A)) (subT C (subExt (π₁ (π₁ id)) (∷ᵐ ? ?))))
  --   → (a : Tm Γ (MSet A))
  --   ---------------------------------------------------------
  --   → Tm Γ {!!}


postulate
  dec : ∀{Γ n} → Tm Γ (𝓤 n) → Ty Γ n
  enc : ∀{Γ n} → Ty Γ n → Tm Γ (𝓤 n)


δ ↑ A = subExt (δ ∘ π₁ id) (π₂ id)

wk = π₁ id
vz = π₂ id
vs x = subt x wk
vsT B = subT B wk

▼ = vz
◁ = vs
◀ = vsT

Ty≡ : {Γ₀ Γ₁ : Cxt}{n : 𝔻 }(Γ₂ : Γ₀ ≡ Γ₁) → Ty Γ₀ n ≡ Ty Γ₁ n
Ty≡ refl = refl

Tms≡ : {Γ₀ Γ₁ : Cxt}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁ : Cxt}(Δ₂ : Δ₀ ≡ Δ₁) → Tms Γ₀ Δ₀ ≡ Tms Γ₁ Δ₁
Tms≡ refl refl = refl

TmΓ≡ : {Γ : Cxt} {n : 𝔻} {A B : Ty Γ n} → (A ≡ B) → Tm Γ A ≡ Tm Γ B
TmΓ≡ {Γ} p = cong (Tm Γ) p

,C= : {Γ₀ Γ₁ : Cxt}{n : 𝔻}(Γ₂ : Γ₀ ≡ Γ₁){A₀ : Ty Γ₀ n}{A₁ : Ty Γ₁ n}(A₂ : A₀ ≡[ Ty≡ Γ₂ ]≡ A₁)
  → _≡_ {A = Cxt} (Γ₀ , A₀) (Γ₁ , A₁)
,C= refl refl = refl



postulate
  idl : {Γ Δ : Cxt} {δ : Tms Γ Δ} → id ∘ δ ≡ δ
  idr : {Γ Δ : Cxt} {δ : Tms Γ Δ} → δ ∘ id ≡ δ
  ass : {Γ Δ Σ Ω : Cxt} {δ : Tms Γ Δ} {σ : Tms Σ Γ} {ν : Tms Ω Σ} →
    (δ ∘ σ) ∘ ν ≡ δ ∘ (σ ∘ ν)
  ,∘ : {Γ Δ Σ : Cxt} {n : 𝔻} {A : Ty Δ n} {δ : Tms Γ Δ} {σ : Tms Σ Γ} {t : Tm Γ (subT A δ)} →
    (subExt δ t) ∘ σ ≡ subExt {Σ} {Δ} {n} {A} (δ ∘ σ) (coe (TmΓ≡ {Σ} {n} {subT (subT A δ) σ} {subT A (δ ∘ σ)} ([][]T {Γ} {Δ} {Σ} {n} {A} {δ} {σ})) (subt t σ))
  π₁β : {Γ Δ : Cxt} {n : 𝔻} {A : Ty Δ n} {δ : Tms Γ Δ} {t : Tm Γ (subT A δ)} →
    π₁ {Γ} {Δ} {n} {A} (subExt δ t) ≡ δ
  πη  : {Γ Δ : Cxt} {n : 𝔻} {A : Ty Δ n} {δ : Tms Γ (Δ , A)} →
    subExt (π₁ δ) (π₂ δ) ≡ δ
  -- TODO
  -- π[]t  : {Γ Δ : Cxt} {n : 𝔻} {A : Ty Δ n} {δ : Tms Γ (Δ , A)} →
  --   subt (π₂ δ) (π₁ id) ≡ ?
  εη  : {Γ : Cxt} {ε' : Tms Γ ⟨⟩} → ε' ≡ ε

{-# REWRITE idl #-}
{-# REWRITE idr #-}
{-# REWRITE ass #-}
{-# REWRITE ,∘ #-}
{-# REWRITE π₁β #-}
{-# REWRITE πη #-}



postulate
  Id[] : ∀{Γ Δ n}{A : Ty Δ n} {a b : Tm Δ A} {δ : Γ ⇒ Δ} → subT (Idᶠ A a b) δ ≡ Idᶠ (subT A δ) (subt a δ) (subt b δ)
  Fin[] : {Γ Δ : Cxt} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subT (Finᶠ n) δ ≡ Finᶠ (subt n δ)

{-# REWRITE Id[] #-}
{-# REWRITE Fin[] #-}
