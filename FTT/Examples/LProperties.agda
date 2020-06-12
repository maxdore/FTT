{-# OPTIONS --rewriting #-}

module FTT.Examples.LProperties where

open import FTT.Base

Ltest : ∀{Γ} → Tm Γ (Πᶠ 0 ⊤ᶠ ℕᶠ)
Ltest = λᶠ (•-ind ℕᶠ ttᶠ zeroᶠ ttᶠ)

Ltest2 : ∀{Γ} → Tm Γ (Πᶠ 0 (Πᶠ 0 ℕᶠ ℕᶠ) (Πᶠ 0 ℕᶠ ℕᶠ))
Ltest2 = λᶠ (•-ind ((Πᶠ 0 ℕᶠ ℕᶠ)) idf ▼ ▼) -- λᶠ (•-ind (Πᶠ 0 ℕᶠ ℕᶠ) vz vz)
  where
  idf : ∀{Γ} → Tm Γ (Πᶠ 0 ℕᶠ ℕᶠ)
  idf = λᶠ vz


⊤Elim : ∀{Γ n}
  → (C : Ty (Γ , ⊤ᶠ) n)
  → (c : Tm Γ (subT C (subExt id ttᶠ)))
  → (a : Tm Γ ⊤ᶠ)
  -------------------------------------
  → (Tm Γ (subT C (subExt id a)))
⊤Elim C c a = •-ind C ttᶠ c a




postulate
  UIPhack : ∀{Γ} → {A : Ty Γ 1} → {a b : Tm Γ A}
    → (subT (Idᶠ A a b) (π₁ (id {Γ , Idᶠ A a b}))) ≡ (Idᶠ (◀ A) (◁ a) (◁ b))


-- {-# REWRITE UIPhack #-}


-- External version
-- UIP : ∀{Γ} → (A : Ty Γ 1) → (a b : Tm Γ A) → (p q : Tm Γ (Idᶠ A a b)) → (Tm Γ (Idᶠ (Idᶠ A a b) p q))
-- UIP {Γ} A a b p q = •-ind {Γ} {0} {(Idᶠ A a b)}
--                         (Idᶠ (Idᶠ {!!} {!!} {!!}) {!!} (coe (TmΓ≡ {!UIPhack!}) ▼))
--                         -- (Idᶠ (Idᶠ (◀ A) (◁ a) (◁ b)) (coe (TmΓ≡ UIPhack) ▼))
--                         p
--                         (reflᶠ {A = Idᶠ A a b} {a = p})
--                         q


-- Internal version
-- UIP : ∀{Γ} → (A : Ty Γ 1) → (Tm (Γ , A , ◀ A ,
--                    (Idᶠ (◀ (◀ A)) (◁ ▼) ▼),
--                    (Idᶠ (◀ (◀ (◀ A))) (◁ (◁ ▼)) (◁ ▼)))
--                    (Idᶠ (Idᶠ (◀ (◀ (◀ (◀ A)))) (◁ (◁ (◁ ▼))) (◁ (◁ ▼))) (◁ ▼) ▼))
-- UIP = {!!}
