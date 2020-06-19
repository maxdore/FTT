{-# OPTIONS --rewriting #-}

module FTT.Base where


open import FTT.Prelude public
open import FTT.Core public
open import FTT.Lemmas public
open import FTT.Eliminators public
open import FTT.Computation public



-- Syntactic sugar

<_> : {Γ : Cxt} {n : ℕ} {A : Ty Γ n} → Tm Γ A → Tms Γ (Γ , A)
< t > = subExt id t

_$_ : ∀{Γ l m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → Tm Γ (Πᶠ l A B) → (u : Tm Γ A) → Tm Γ (subT B < u >)
t $ u = subt (appᶠ t) < u >


Πᶠc : {Γ : Cxt} {m n : ℕ} → (l : ℕ) → (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ l
Πᶠc {Γ} {m} {n} l A B = Πᶠ l A (vsT B)


-- non-dependent product (weird syntax since we have level parameter...()
Σᶠc : {Γ : Cxt} {m n : ℕ} → (l : ℕ) → (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ l
Σᶠc {Γ} {m} {n} l A B = Σᶠ l A (vsT B)


pred : ∀{Γ} → Tm Γ ℕᶠ → Tm Γ ℕᶠ
pred x = ℕ-ind ℕᶠ zeroᶠ ▼ x

-- Identity types

-- sym : ∀{Γ n} {A : Ty Γ n} {a b : Tm Γ A} → (Tm Γ (Idᶠ A a b)) → (Tm Γ (Idᶠ A b a))
-- sym {Γ} {n} {A} {a} {b} x = {!Id-ind!}

-- TODO trans


-- appf : ∀{Γ l m n} {A : Ty Γ m} {B : Ty Γ n} → Tm Γ (Πᶠc {Γ} {m} {n} l A B) → Tm Γ A → Tm Γ B
-- appf f a = f $ a

-- https://math.stackexchange.com/a/673003/470161
-- Σ : ∀{Γ i j} → (l : ℕ) → (A : Ty Γ i) → (B : Ty (Γ , A) j) → {!!}
-- Σ {Γ} {i} {j} l A B = {k : ℕ} → (C : Ty Γ k) → (x : Tm Γ A) → {!!}




-- Projections!

-- Σπ₁simple : ∀{Γ} → Tm (Γ , Σᶠ 1 ℕᶠ ⊤ᶠ) (⊤ᶠ)
-- Σπ₁simple = Σ-ind ⊤ᶠ ▼ ▼

-- π₁ᶠ : ∀ {Γ l j} → {A : Ty Γ l} → {B : Ty (Γ , A) j} → {p : Tm Γ (Σᶠ l A B)} → Tm Γ A
-- π₁ᶠ {Γ} {l} {j} {A} {B} {p} = Σ-ind (◀ A) (◁ ▼) p

-- π₂ᶠ : ∀ {Γ l i j} → {A : Ty Γ i} → {B : Ty (Γ , A) j} → Tm (Γ , Σᶠ l A B) {!B!}
-- π₂ᶠ {Γ} {l} {i} {j} {A} {B} = Σ-ind {!!} {!!} {!!}
