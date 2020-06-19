{-# OPTIONS --rewriting #-}

module FTT.Computation where

open import FTT.Prelude
open import FTT.Core
open import FTT.Lemmas
open import FTT.Eliminators

-- Term substitutions
postulate
  [id]t : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {t : Tm Δ A} {δ : Tms Γ Δ} →
    subt t id ≡[ TmΓ≡ [id]T ]≡ t
  [][]t : {Γ Δ Σ : Cxt} {n : ℕ} {A : Ty Δ n} {t : Tm Δ A} {δ : Tms Γ Δ} {σ : Tms Σ Γ} →
    subt (subt t δ) σ ≡ subt t (δ ∘ σ)  -- without rewrite ≡[ TmΓ≡ ([][]T {Γ} {Δ} {Σ} {n} {A} {δ} {σ}) ]≡
  π₂β : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ Δ} {a : Tm Γ (subT A δ)} →
    π₂ {Γ} {Δ} {n} {A} (subExt δ a) ≡ a

  -- TODO DONT WE NEED δ : (Γ , A) Δ ???
  λ[] : ∀ {Γ l m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm (Γ , A) B}
    {δ : (Γ , A) ⇒ Γ}
    ---------------------------------------------------------
    → subt (λᶠ {Γ} {l} {m} {n} {A} {B} t) δ ≡ λᶠ (subt t (δ ↑ A))

  -- TODO
  -- pair[] : ∀ {Γ l m n}
  --   {A : Ty Γ m}
  --   {B : Ty (Γ , A) n}
  --   {a : Tm Γ A}
  --   {b : Tm Γ (subT B (subExt id a))}
  --   {δ : Tms (Γ , A) Γ}
  --   ---------------------------------------------------------
  --   → subt (pair {Γ} {l} {m} {n} {A} {B} a b) δ ≡ pair (subt a δ) (subt b {!δ!})

  tt[] : ∀{Γ Δ} {δ : Tms Γ Δ} → subt ttᶠ δ ≡ ttᶠ
  zero[] : ∀{Γ Δ} {δ : Tms Γ Δ} → subt zeroᶠ δ ≡ zeroᶠ
  suc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (sucᶠ n) δ ≡ sucᶠ (subt n δ)

  -- A⁰-ind[] : ∀ {Γ Δ n} {δ : Tms Γ Δ}
  --     {A : Ty Δ 0}
  --     {C : Ty (Δ , A) n}
  --     {a : Tm Δ A}
  --     {c : Tm Δ (subT C (subExt id a))}
  --   ---------------------------------------------------------
  --   → subt (A⁰-ind C a c) δ ≡ A⁰-ind (subT C {!δ ↑ A!}) (subt a δ) (subt c δ)


  -- ⊤-ind[] : ∀ {Γ Δ n} {δ : Tms (Γ , ⊤ᶠ) (Δ)}
  --     → {C : Ty (Δ , ⊤ᶠ) n}
  --     → {c : Tm Δ (subT C (subExt id ttᶠ))}
  --     → {a : Tm Δ ⊤ᶠ}
  --     ---------------------------------------------------------
  --     → subt (⊤-ind C c a) δ ≡ ⊤-ind {Γ , ⊤ᶠ} {n} (subT C (δ ↑ ⊤ᶠ)) ? ?

-- → subt (⊤-ind C c a) δ ≡[ {!!} ]≡ ⊤-ind {Γ , ⊤ᶠ} {n} (subT C (δ ↑ ⊤ᶠ)) {!(subT (subT C (δ ↑ ⊤ᶠ)) (subExt id ttᶠ))!} {!!}
  --     → subt (⊤-ind C c a) δ ≡[ TmΓ≡ {!!} ]≡ ⊤-ind {Γ} {n} {!!} {!!} {!!}
  --     -- ≡[ TmΓ≡ {!!} ]≡ ⊤-ind {Γ , ⊤ᶠ} {n} (subT C (δ ↑ ⊤ᶠ)) (coe (TmΓ≡ {!!}) (subt c δ)) (subt a δ)

-- Tm (Γ , ⊤ᶠ) (subT (subT C (subExt id a)) δ) ≡
-- Tm (Γ , ⊤ᶠ) (subT (subT C (δ ↑ ⊤ᶠ)) (subExt id (subt a δ)))

  -- ℕ-ind[] : ∀{Γ Δ n} {δ : Tms Γ Δ}
  --   {C : Ty (Δ , ℕᶠ) n}
  --   {c₀ : Tm Δ (subT C (subExt id zeroᶠ))}
  --   {cₛ : Tm (Δ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz)))}
  --   {n : Tm Δ ℕᶠ}
  --   ---------------------------------------------------------
  --   → subt (ℕ-ind C c₀ cₛ n) δ ≡[ {!!} ]≡ ℕ-ind
  --     (subT C (δ ↑ ℕᶠ))
  --     (coe (TmΓ≡ (hack2 {Γ} {Δ} {{!n!}} {δ} {C})) (subt c₀ δ))
  --     {!!}
  --     (subt n δ)
  --   → subt (ℕ-ind C c₀ cₛ n) δ ≡[ {!!} ]≡ ℕ-ind (subT C (subExt {!!} {!!})) (subt c₀ δ) (subt cₛ (δ ↑ ℕᶠ)) (subt n δ)


{-# REWRITE [id]t #-}
{-# REWRITE [][]t #-}
{-# REWRITE π₂β #-}
{-# REWRITE λ[] #-}
{-# REWRITE tt[] #-}
{-# REWRITE zero[] #-}
{-# REWRITE suc[] #-}


--   fzero[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (fzeroᶠ {Δ} {n}) δ ≡ fzeroᶠ {Γ} {subt n δ}
--   fsuc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} {i : Tm Δ (Finᶠ n)} → subt (fsucᶠ {Δ} {n} i) δ ≡ fsucᶠ {{!!}} {{!!}} {!!}

  -- fsuc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (sucᶠ n) δ ≡ sucᶠ (subt n δ)

  -- suc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (sucᶠ n) δ ≡ sucᶠ (subt n δ)

-- Computation rules
postulate

  •β : ∀{Γ n}
    {A : Ty Γ 0}
    {C : Ty (Γ , A) n}
    {a : Tm Γ A}
    {c : Tm Γ (subT C (subExt id a))}
    ---------------------------------------------------------
    → •-ind C a c a ≡ c

  Πβ : ∀{Γ l m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm (Γ , A) B}
    ---------------------------------------------------------
    → appᶠ {Γ} {l} {m} {n} {A} {B} (λᶠ t) ≡ t

  Πη : ∀{Γ l m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {f : Tm Γ (Πᶠ l A B)}
    ---------------------------------------------------------
    → λᶠ (appᶠ f) ≡ f

  -- Σβ : ∀{Γ l i j n}
  --   {A : Ty Γ i}
  --   {B : Ty (Γ , A) j}
  --   {C : Ty (Γ , (Σᶠ l A B)) n}
  --   {g : Tm (Γ , A , subT B (subExt wk vz)) (subT C (subExt (wk ∘ wk) (pair (◁ ▼) ▼)))}
  --   {a : Tm Γ A}
  --   {b : Tm Γ (subT B (subExt id a))}
  --   ---------------------------------------------------------
  --   → split {A = A} {B = B} C g (pair a b)
  --       ≡[ TmΓ≡ (Σβhack {Γ} {l} {i} {j} {n} {A} {B} {C} {g} {a} {b}) ]≡
  --     subt g (subExt (subExt id a) b)

  ⊤β : ∀{Γ n}
    {C : Ty (Γ , ⊤ᶠ) n}
    {c : Tm Γ (subT C (subExt id ttᶠ))}
    ---------------------------------------------------------
    → ⊤-ind C c ttᶠ ≡ c

  ℕβ₀ : ∀{Γ n}
    {C : Ty (Γ , ℕᶠ) n}
    {c₀ : Tm Γ (subT C (subExt id zeroᶠ))}
    {cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz)))}
    ---------------------------------------------------------
    → ℕ-ind C c₀ cₛ zeroᶠ ≡ c₀

  ℕβₙ : ∀{Γ n}
    {C : Ty (Γ , ℕᶠ) n}
    {c₀ : Tm Γ (subT C (subExt id zeroᶠ))}
    {cₛ : Tm (Γ , ℕᶠ) (subT C (subExt (π₁ id) (sucᶠ vz)))}
    {n : Tm Γ ℕᶠ}
    ---------------------------------------------------------
    → ℕ-ind {Γ} C c₀ cₛ (sucᶠ n) ≡ subt cₛ (subExt id n)


  -- ⊥β : TODO ABSURDITY
  -- ⊤β : {Γ Δ : Cxt} {t : Tm Δ ⊤ᶠ} {δ : Tms Γ Δ} → ⊤-ind t ≡ subT {!!} {!!}


{-# REWRITE •β #-}
{-# REWRITE Πβ #-}
{-# REWRITE Πη #-}
{-# REWRITE ⊤β #-}
{-# REWRITE ℕβ₀ #-}
-- {-# REWRITE ℕβₙ #-}












