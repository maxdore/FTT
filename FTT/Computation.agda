{-# OPTIONS --rewriting #-}

module FTT.Computation where

open import FTT.Prelude
open import FTT.Core
open import FTT.SubProp
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
  λ[] : {Γ : Cxt} {l m n : ℕ} {A : Ty Γ m} {B : Ty (Γ , A) n} {t : Tm (Γ , A) B} {δ : Tms (Γ , A) Γ} →
    subt (λᶠ {Γ} {l} {m} {n} {A} {B} t) δ ≡ λᶠ (subt t (δ ↑ A))

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



-- postulate
-- ⊤-ind[] : ∀ {Γ Δ n} {δ : Tms (Γ , ⊤ᶠ) Δ}
--     → {C : Ty (Δ , ⊤ᶠ) n}
--     → {c : Tm Δ (subT C (subExt id ttᶠ))}
--     → {a : Tm Δ ⊤ᶠ}
--     ---------------------------------------------------------
--     → subt (⊤-ind C c a) δ ≡ {!!}
    -- → subt (⊤-ind C c a) δ ≡ ⊤-ind (coe (Ty≡ (,C= (,C= refl refl) ⊤[])) (subT C (δ ↑ ⊤ᶠ))) ? ? -- (subt c δ) (subt a δ)

--   fzero[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (fzeroᶠ {Δ} {n}) δ ≡ fzeroᶠ {Γ} {subt n δ}
--   fsuc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} {i : Tm Δ (Finᶠ n)} → subt (fsucᶠ {Δ} {n} i) δ ≡ fsucᶠ {{!!}} {{!!}} {!!}

  -- fsuc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (sucᶠ n) δ ≡ sucᶠ (subt n δ)

  -- suc[] : ∀{Γ Δ} {δ : Tms Γ Δ} {n : Tm Δ ℕᶠ} → subt (sucᶠ n) δ ≡ sucᶠ (subt n δ)

-- Computation rules
postulate
  A⁰β : ∀{Γ n}
    {A : Ty Γ 0}
    {C : Ty (Γ , A) n}
    {c : Tm (Γ , A) C}
    {a : Tm Γ A}
    ---------------------------------------------------------
    → A⁰-ind C c a ≡ subt c (subExt id a)

  -- TODO REWRITE EVERYTHING TO • !!!
  -- Contract : ∀{Γ}
  --   {A : Ty Γ 0}
  --   {a b : Tm Γ A}
  --   ---------------------------------------------------------
  --   → a ≡ b

  Πβ : ∀{Γ l m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm (Γ , A) B}
    ---------------------------------------------------------
    → appᶠ {Γ} {l} {m} {n} {A} {B} (λᶠ t) ≡ t

  Πη : ∀{Γ l m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm Γ (Πᶠ l A B)}
    ---------------------------------------------------------
    → λᶠ (appᶠ t) ≡ t

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


{-# REWRITE A⁰β #-}
{-# REWRITE Πβ #-}
{-# REWRITE Πη #-}
{-# REWRITE ⊤β #-}
{-# REWRITE ℕβ₀ #-}
{-# REWRITE ℕβₙ #-}








<_> : {Γ : Cxt} {n : ℕ} {A : Ty Γ n} → Tm Γ A → Tms Γ (Γ , A)
< t > = subExt id t -- (coe (TmΓ≡ (sym {!subT!})) t)

_$_ : ∀{Γ l m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → Tm Γ (Πᶠ l A B) → (u : Tm Γ A) → Tm Γ (subT B < u >)
t $ u = subt (appᶠ t) < u >




-- TODO PROVE BELOW POSTULATE WITH THESE LEMMAS
-- π₁= : ∀{Γ₀ Γ₁ n}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁}(Δ₂ : Δ₀ ≡ Δ₁)
--   {A₀ : Ty Δ₀ n}{A₁ : Ty Δ₁ n}(A₂ : A₀ ≡[ Ty≡ Δ₂ ]≡ A₁)
--   {δ₀ : Tms Γ₀ (Δ₀ , A₀)}{δ₁ : Tms Γ₁ (Δ₁ , A₁)}(δ₂ : δ₀ ≡[ Tms≡ Γ₂ (,C= Δ₂ A₂) ]≡ δ₁)
--   → π₁ δ₀ ≡[ Tms≡ Γ₂ Δ₂ ]≡ π₁ δ₁
-- π₁= refl refl refl refl = refl

-- π₁=' : ∀{Γ Δ n}{A : Ty Δ n}{δ₀ δ₁ : Tms Γ (Δ , A)}(δ₂ : δ₀ ≡ δ₁) → π₁ δ₀ ≡ π₁ δ₁
-- π₁=' δ₂ = π₁= refl refl refl δ₂

-- π₁∘ : ∀{Γ Δ Θ n}{A : Ty Δ n}{δ : Tms Γ (Δ , A)}{ρ : Tms Θ Γ} → π₁ δ ∘ ρ ≡ π₁ (δ ∘ ρ)
-- π₁∘ {Γ}{Δ}{Θ}{n}{A}{δ}{ρ} = π₁β {Θ} {Δ} {n} {A} {π₁ δ ∘ ρ} {{!!}} ⁻¹ ◾ π₁=' (,∘ ⁻¹) ◾ π₁=' (cong (λ z → (z ∘ ρ)) πη)

postulate
  nondepext : ∀{Γ m n} {A : Ty Γ m} {B : Ty Γ n} {a : Tm Γ A} → subT (vsT B) < a > ≡ B
-- nondepext = [][]T ◾ cong (subT _) (π₁∘ ◾ (cong π₁ idl ◾ (π₁β ◾ {![id]T!}))) -- ◾ ?
{-# REWRITE nondepext #-}

Πᶠc : {Γ : Cxt} {m n : ℕ} → (l : ℕ) → (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ l
Πᶠc {Γ} {m} {n} l A B = Πᶠ l A (vsT B)

-- appf : ∀{Γ l m n} {A : Ty Γ m} {B : Ty Γ n} → Tm Γ (Πᶠc {Γ} {m} {n} l A B) → Tm Γ A → Tm Γ B
-- appf f a = f $ a

