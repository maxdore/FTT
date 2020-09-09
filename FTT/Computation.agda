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
    subt (subt t δ) σ ≡ subt t (δ ∘ σ)
  π₂β : {Γ Δ : Cxt} {n : ℕ} {A : Ty Δ n} {δ : Tms Γ Δ} {a : Tm Γ (subT A δ)} →
    π₂ {Γ} {Δ} {n} {A} (subExt δ a) ≡ a

  enc[] : ∀{Γ Δ n} {δ : Tms Γ Δ}
    {A : Ty Δ n}
    → subt (enc A) δ ≡ enc (subT A δ)

  λ[] : ∀ {Γ m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm (Γ , A) B}
    {δ : (Γ , A) ⇒ Γ}
    ---------------------------------------------------------
    → subt (λᶠ {Γ} {m} {n} {A} {B} t) δ ≡ λᶠ (subt t (δ ↑ A))

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

  -- TODO
  -- U[] : ... subt (𝓤 n ℓ) δ → 𝓤 n l
  -- dec[] : ... subt (dec a) δ → dec (subt a)


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
{-# REWRITE enc[] #-}
{-# REWRITE λ[] #-}
{-# REWRITE tt[] #-}
{-# REWRITE zero[] #-}
{-# REWRITE suc[] #-}


-- Computation rules
postulate

  Lβ : ∀{Γ n}
    {A : Ty Γ 0}
    {C : Ty (Γ , A) n}
    {a : Tm Γ A}
    {c : Tm Γ (subT C (subExt id a))}
    ---------------------------------------------------------
    → L C a c a ≡ c

  𝓤β : ∀{Γ n}
    {A : Ty Γ n}
    ---------------------------------------------------------
    → dec (enc A) ≡ A

  𝓤η : ∀{Γ n}
    {A : Tm Γ (𝓤 n)}
    ---------------------------------------------------------
    → enc (dec A) ≡ A

  Πβ : ∀{Γ m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {t : Tm (Γ , A) B}
    ---------------------------------------------------------
    → appᶠ {Γ} {m} {n} {A} {B} (λᶠ t) ≡ t

  Πη : ∀{Γ m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {f : Tm Γ (Πᶠ A B)}
    ---------------------------------------------------------
    → λᶠ (appᶠ f) ≡ f

  Σβ₁ : ∀{Γ m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {a : Tm Γ A}
    {b : Tm Γ (subT B (subExt id a))}
    ---------------------------------------------------------
    → fst {Γ} {m} {n} {A} {B} (pair a b) ≡ a

  Σβ₂ : ∀{Γ m n}
    {A : Ty Γ m}
    {B : Ty (Γ , A) n}
    {a : Tm Γ A}
    {b : Tm Γ (subT B (subExt id a))}
    ---------------------------------------------------------
    → snd {Γ} {m} {n} {A} {B} (pair a b)
      ≡ coe (TmΓ≡ (cong (subT B) (cong (subExt id) (Σβ₁ ⁻¹)))) b

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


{-# REWRITE Lβ #-}
{-# REWRITE 𝓤β #-}
{-# REWRITE 𝓤η #-}
{-# REWRITE Πβ #-}
{-# REWRITE Πη #-}
{-# REWRITE ⊤β #-}
{-# REWRITE ℕβ₀ #-}
{-# REWRITE ℕβₙ #-}
{-# REWRITE Σβ₁ #-}
{-# REWRITE Σβ₂ #-}











