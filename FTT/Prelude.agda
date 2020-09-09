{-# OPTIONS --rewriting #-}

module FTT.Prelude where

open import Agda.Primitive public

-- Cubical intro
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Nat


-- Plain intro
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n

supℕ : ℕ → ℕ → ℕ
supℕ zero n = n
supℕ m zero = m
supℕ (suc m) (suc n) = suc (supℕ m n)

coe : ∀{ℓ}{A B : Set ℓ} → A ≡ B → A → B
coe refl a = a

cong : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → f a₀ ≡ f a₁
cong f refl = refl

transport : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y
transport P p a = coe (cong P p) a

-- sym : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
-- sym refl = refl

_⁻¹ : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

_◾_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

infixl 4 _◾_

{-# BUILTIN REWRITE _≡_ #-}

_≡[_]≡_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_
