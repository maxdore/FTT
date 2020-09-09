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

_$_ : ∀{Γ m n} {A : Ty Γ m} {B : Ty (Γ , A) n} → Tm Γ (Πᶠ A B) → (u : Tm Γ A) → Tm Γ (subT B < u >)
t $ u = subt (appᶠ t) < u >

Πᶠc : {Γ : Cxt} {m n : ℕ} → (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ n
Πᶠc {Γ} {m} {n} A B = Πᶠ A (vsT B)

Σᶠc : {Γ : Cxt} {m n : ℕ} (A : Ty Γ m) → (B : Ty Γ n) → Ty Γ (sup𝔻 m n)
Σᶠc {Γ} {m} {n} A B = Σᶠ A (vsT B)


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
