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

Σᶠc : {Γ : Cxt} {m n : ℕ} → (l : ℕ) → (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ l
Σᶠc {Γ} {m} {n} l A B = Σᶠ l A (vsT B)


-- 𝓤ⁿ has dimension n+1
𝓤ⁿ:𝓤ⁿ⁺¹ : ∀{Γ} → (n : ℕ) → Tm Γ (𝓤 (suc𝔻 n))
𝓤ⁿ:𝓤ⁿ⁺¹ {Γ} n = enc (𝓤 n)


-- Basic properties of identity types. These follow as usual from J.

-- sym : ∀{Γ n} {A : Ty Γ n} {a b : Tm Γ A} → (Tm Γ (Idᶠ A a b)) → Tm Γ (Idᶠ A b a)
-- sym {Γ} {n} {A} {a} {b} p = coe {!!} (Id-ind {C = Idᶠ (◀ (◀ (◀ A))) (◁ ▼) (◁ (◁ ▼))} (coe {!!} (reflᶠ {a = ▼})) a b p)

-- sym : ∀{Γ n} {A : Ty Γ n} {a b : Tm Γ A} → Tm (Γ , (Idᶠ A a b )) (Idᶠ (◀ A) (◁ b) (◁ a))
-- sym {Γ} {n} {A} {a} {b} = Id-ind {C = Idᶠ (◀ (◀ (◀ (◀ A)))) (◁ ▼) {!!}} {!!} {!!} {!!} ▼

-- sym : ∀{Γ n} {A : Ty Γ n} → Tm (Γ , A , ◀ A , (Idᶠ (◀ (◀ A)) (◁ ▼) ▼ )) (Idᶠ (◀ (◀ (◀ A))) (◁ ▼) (◁ (◁ ▼)))
-- sym {Γ} {n} {A} = Id-ind {C = Idᶠ (◀ (◀ (◀ (◀ (◀ {!!}))))) {!!} {!!}} {!!} {!!} {!!} {!!}

-- TODO trans

postulate
  subst : ∀{Γ m n} {A : Ty Γ m} {x y : Tm Γ A}
    → (B : Ty (Γ , A) n) → (p : Tm Γ (Idᶠ A x y)) → Tm Γ (subT B (subExt id x)) → Tm Γ (subT B (subExt id y))
