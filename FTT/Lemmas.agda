{-# OPTIONS --rewriting #-}

module FTT.Lemmas where

open import FTT.Prelude
open import FTT.Core



id↑ : ∀{Γ n}{A : Ty Γ n} → id ↑ A ≡ id {Γ , A}
id↑ = refl

π₁= : ∀{Γ₀ Γ₁ n}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁}(Δ₂ : Δ₀ ≡ Δ₁)
  {A₀ : Ty Δ₀ n}{A₁ : Ty Δ₁ n}(A₂ : A₀ ≡[ Ty≡ Δ₂ ]≡ A₁)
  {δ₀ : Tms Γ₀ (Δ₀ , A₀)}{δ₁ : Tms Γ₁ (Δ₁ , A₁)}(δ₂ : δ₀ ≡[ Tms≡ Γ₂ (,C= Δ₂ A₂) ]≡ δ₁)
  → π₁ δ₀ ≡[ Tms≡ Γ₂ Δ₂ ]≡ π₁ δ₁
π₁= refl refl refl refl = refl

π₁=' : ∀{Γ Δ n}{A : Ty Δ n}{δ₀ δ₁ : Tms Γ (Δ , A)}(δ₂ : δ₀ ≡ δ₁) → π₁ δ₀ ≡ π₁ δ₁
π₁=' δ₂ = π₁= refl refl refl δ₂


-- π₁∘ : ∀{Γ Δ Θ n}{A : Ty Δ n}{δ : Tms Γ (Δ , A)}{ρ : Tms Θ Γ}
--   → π₁ δ ∘ ρ ≡ π₁ (δ ∘ ρ)
-- π₁∘ {Γ}{Δ}{Θ}{n}{A}{δ}{ρ} = (π₁β {Θ} {Δ} {n} {A} {π₁ δ ∘ ρ} {_}) ⁻¹
--                         ◾ π₁=' (,∘ ⁻¹)
--                         ◾ π₁=' (cong (λ x → x ∘ ρ) πη)

-- π₁id∘ : ∀{Γ Δ n}{A : Ty Δ n}{ρ : Tms Γ (Δ , A)}
--   → π₁ id ∘ ρ ≡ π₁ ρ
-- π₁id∘ = π₁∘ ◾ π₁=' idl

postulate
  wk∘<> : ∀{Γ i}{A : Ty Γ i}{u : Tm Γ A} → (π₁ id) ∘ (subExt id u) ≡ id
-- wk∘<> = π₁id∘ ◾ π₁β

  natHack : {Γ : Cxt} {n : Tm Γ ℕᶠ} → subExt id (sucᶠ n) ≡ (subExt (π₁ id) (sucᶠ (π₂ id)) ∘ subExt id n)

{-# REWRITE wk∘<> #-}
{-# REWRITE natHack #-}

postulate
  Σhack : ∀ {Γ n l i j}
    {A : Ty Γ i}
    {B : Ty (Γ , A) j}
    {C : Ty (Γ , Σᶠ l A B) n}
    ---------------------------------------------------------
    -- → π₁ (id {Γ , A , B}) ≡ (((π₁ (id {Γ , A})) ∘ (π₁ (id {Γ , A , B}))) ↑ A) ∘ subExt id (vs vz)
    -- → π₁ id ≡ subExt ((π₁ id ∘ (π₁ id ∘ π₁ id)) ∘ subExt id (vs vz))
    → subT B (π₁ (id {Γ , A , B})) ≡ subT (subT B ((wk ∘ wk) ↑ A)) (subExt id (vs vz))



{-# REWRITE Σhack #-}

-- Σhack2 : ∀{Γ i j}
--   {A : Ty Γ i}
--   {B : Ty (Γ , A) j}
--   {a : Tm Γ A}
--   {b : Tm Γ (subT B (subExt id a))}
--   ---------------------------------------------------------
--   → subExt id (pair a b) ≡ (subExt (wk ∘ wk) (pair (◁ ▼) ▼) ∘ subExt (subExt id a) b)



-- From TT/Core/Laws

-- see also TT/Core/Laws/JM

-- postulate
--   π₁∘ : ∀{Γ Δ Σ n}{A : Ty Δ n}{δ : Tms Γ (Δ , A)}{ρ : Tms Σ Γ}
--     → π₁ δ ∘ ρ ≡ π₁ (δ ∘ ρ)
-- -- π₁∘ {Γ}{Δ}{Σ}{A}{δ}{ρ} = π₁β ⁻¹ ◾ π₁=' (,∘ ⁻¹) ◾ π₁=' refl -- (cong (λ z → (z ∘ ρ)) πη)

--   π₁idβ : ∀{Γ Δ i}{ρ : Tms Γ Δ}{A : Ty Δ i}{t : Tm Γ (subT A ρ)}
--     → π₁ (id {Δ , A}) ∘ (subExt ρ t) ≡ ρ
-- -- π₁idβ = π₁∘ ◾ π₁=' idl ◾ π₁β

--   ∘π₁id : ∀{Γ Δ i}{ρ : Tms Γ Δ}{A : Ty Δ i}
--     → ρ ∘ π₁ {A = subT A ρ} id ≡ π₁ id ∘ (ρ ↑ A)
--   -- ∘π₁id {Γ}{Δ}{ρ}{A} = π₁β ⁻¹ ◾ ap π₁ idl ⁻¹ ◾ π₁∘ ⁻¹

--   π₁id∘ : ∀{Γ Δ i}{A : Ty Δ i}{ρ : Tms Γ (Δ , A)}
--     → π₁ id ∘ ρ ≡ π₁ ρ
--   -- π₁id∘ = π₁∘ ◾ π₁=' idl

-- {-# REWRITE π₁∘ #-}
-- {-# REWRITE π₁idβ #-}
-- {-# REWRITE ∘π₁id #-} LEADS TO NONTERMINATING TYPECHECKING!
-- {-# REWRITE π₁id∘ #-}



-- postulate
--   -- wk∘<> : ∀{Γ i}{A : Ty Γ i}{u : Tm Γ A} → (π₁ id) ∘ (subExt id u) ≡ id
--   -- wk∘<> = π₁id∘ ◾ π₁β

--   [wk][id,] : ∀{Γ i j}{A : Ty Γ i}{B : Ty Γ j}{u : Tm Γ (subT B id)}
--     → A ≡ subT (subT A wk) (subExt id u)
--   -- [wk][id,] {Γ}{A}{B}{u} = [id]T ⁻¹ ◾ ap (_[_]T A) ( π₁β ⁻¹ ◾ π₁id∘ ⁻¹) ◾ [][]T ⁻¹

--   [wk][,] : ∀{Γ Δ i j}{σ : Tms Γ Δ}{A : Ty Δ i}{B : Ty Δ j}{u : Tm Γ (subT B σ)}
--     → subT (subT A (π₁ (id {Δ , B}))) (subExt σ u) ≡ subT A σ
--   -- [wk][,] {Γ}{Δ}{σ}{A}{B}{u} = [][]T ◾ A[]T= (π₁id∘ ◾ π₁β)

--   [wk][wk][id,,] : ∀ {Γ i j k}{A : Ty Γ i}{B : Ty Γ j}{C : Ty (Γ , B) k}
--     {u : Tm Γ (subT B id)}{v : Tm Γ (subT C (subExt id u))}
--     → A ≡ subT (subT (subT A (π₁ (id {Γ , B}))) (π₁ (id {Γ , B , C}))) (subExt (subExt id u) v)
--   -- [wk][wk][id,,] {Γ}{A}{B}{C}{u}{v}
--   -- = [id]T ⁻¹
--   -- ◾ ap
--   -- (_[_]T A)
--   -- ( π₁β ⁻¹
--   -- ◾ ap π₁ (π₁β ⁻¹ ◾ π₁id∘ ⁻¹)
--   -- ◾ π₁id∘ ⁻¹)
--   -- ◾ [][]T ⁻¹
--   -- ◾ [][]T ⁻¹

--   [wk][^]T : ∀{Γ Θ i j}{A : Ty Γ i}{σ : Tms Θ Γ}{B : Ty Γ j}
--     → subT (subT B wk) (σ ↑ A) ≡ subT (subT B σ) wk
--   -- [wk][^]T = [][]T ◾ []T=' refl refl π₁idβ ◾ [][]T ⁻¹

--   []T∘ : ∀{Γ Δ Θ i}{ν : Tms Γ Δ}{σ : Tms Δ Θ}{A : Ty Δ i}{B : Ty Θ i} (p : A ≡ subT B σ)
--     → subT A ν ≡ subT B (σ ∘ ν)
--   -- []T∘ p = [σ]T= p ◾ [][]T

--   [][]T∘ : ∀{Γ Δ Δ' Θ i}{σ : Tms Γ Δ}{ν : Tms Δ Θ}{σ' : Tms Γ Δ'}{ν' : Tms Δ' Θ}
--     → ν ∘ σ ≡ ν' ∘ σ' → {A : Ty Θ i}
--     → subT (subT A ν) σ ≡ subT (subT A ν') σ'
--   -- [][]T∘ p = [][]T ◾ (A[]T= p ◾ [][]T ⁻¹)

-- {-# REWRITE [wk][,] #-}
-- {-# REWRITE [wk][^]T #-}


-- postulate
--   π₁id∘coe' : ∀{Δ Γ₀ Γ₁ n}{A : Ty Δ n}(Γ₂ : Γ₀ ≡ Γ₁){σ : Tms Γ₀ (Δ , A)}
--     → π₁ id ∘ σ ≡ π₁ σ

-- {-# REWRITE π₁id∘coe' #-}

-- Own Lemmas

  -- error message: π₁ (π₁ id) != subExt (π₁ (π₁ id) ∘ π₁ id) (π₂ id)
  -- pis : ∀{Γ i j}{A : Ty Γ i}{B : Ty (Γ , A) j}
  --   → π₁ (π₁ (id {Γ , A , B , ◀ (◀ A)})) ≡ subExt (π₁ (π₁ (id {Γ , A , B})) ∘ π₁ (id {Γ , A , B , ◀ (◀ A)})) (π₂ (id {Γ , A , B , ◀ (◀ A)}))

  -- error message: (π₁ id ∘ subExt id n) != id

  -- error message: δ != δ ∘ (π₁ id ∘ subExt id ttᶠ)
  -- subsumed by wk∘<>
  -- ⊤hack : ∀ {Γ Δ} {δ : Γ ⇒ Δ} → subExt id ttᶠ ≡ (subExt (π₁ id) (π₂ id) ∘ subExt δ ttᶠ)
  -- ⊤hack : ∀ {Γ} → π₁ (id {Γ , ⊤ᶠ}) ∘ subExt (id {Γ}) ttᶠ ≡ id

  -- ⊤hack : ∀{Γ Δ n} {δ : Γ ⇒ Δ} {C : Ty (Δ , ⊤ᶠ) n} {a : Tm Δ ⊤ᶠ}
  --   → (subT (subT C (δ ↑ ⊤ᶠ)) (subExt id (subt a δ))) ≡ subT (subT C (subExt id a)) δ
       -- subT (subT C (δ ↑ ⊤ᶠ)) (subExt id (subt a δ)) ≡ subT (subT C (subExt id a)) δ 
-- ⊤hack {Γ} {Δ} {n} {δ} {C} {a} = refl ◾ ({!refl!} ◾ refl)

-- {-# REWRITE pis #-}
-- {-# REWRITE ⊤hack #-}



-- postulate
--   Σβhack : ∀{Γ l i j n}
--     {A : Ty Γ i}
--     {B : Ty (Γ , A) j}
--     {C : Ty (Γ , (Σᶠ l A B)) n}
--     {g : Tm (Γ , A , subT B (subExt wk vz)) (subT C (subExt (wk ∘ wk) (pair (◁ ▼) ▼)))}
--     {a : Tm Γ A}
--     {b : Tm Γ (subT B (subExt id a))}
--     ---------------------------------------------------------
--     -- → (π₁ id ∘ (π₁ (id {Γ , A , B}) ∘ subExt (subExt id a) b)) ≡ id
--     → subT C (subExt id (pair a b))
--        ≡ subT (subT C (subExt (wk ∘ (π₁ (id {Γ , A , B}))) (pair (◁ ▼) ▼))) (subExt (subExt id a) b)

-- {-# REWRITE Σβhack #-}


-- from TT/Core
-- [_,_] : {A : ∀{Γ} → Ty Γ}(A[] : ∀{Γ Θ}{σ : Tms Γ Θ} → A [ σ ]T ≡ A)(t : ∀{Γ} → Tm Γ A → Tm Γ A)
-- {Γ : Con} → Tms (Γ , A) (Γ , A)
-- [ A[] , t ] = wk ,s coe (TmΓ= (A[] ⁻¹)) (t (coe (TmΓ= A[]) vz))






-- π₁id∘coe⁻¹ : ∀{Δ Γ}{A₀ A₁ : Ty Δ}(A₂ : A₀ ≡ A₁){σ : Tms Γ (Δ , A₁)}
--   → π₁ id ∘ coe (TmsΓ-= (,C≃ refl (to≃ A₂) ⁻¹)) σ ≃ π₁ σ



-- []T=′ : {Γ₀ Γ₁ : Cxt}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁ : Cxt}(Δ₂ : Δ₀ ≡ Δ₁)
--   {n : ℕ}{A₀ : Ty Δ₀ n}{A₁ : Ty Δ₁ n}(A₂ : A₀ ≡[ Ty≡ Δ₂ ]≡ A₁)
--   {σ₀ : Tms Γ₀ Δ₀}{σ₁ : Tms Γ₁ Δ₁}(σ₂ : σ₀ ≡[ Tms≡ Γ₂ Δ₂ ]≡ σ₁)
--   → subT A₀ σ₀ ≡[ Ty≡ Γ₂ ]≡ subT A₁ σ₁
-- []T=′ refl refl refl refl = refl

-- []T= : {Γ₀ Γ₁ : Cxt}(Γ₂ : Γ₀ ≡ Γ₁){Δ₀ Δ₁ : Cxt}(Δ₂ : Δ₀ ≡ Δ₁)
--   {n : ℕ}{A₀ : Ty Δ₀ n}{A₁ : Ty Δ₁ n}(A₂ : A₀ ≡[ Ty≡ Δ₂ ]≡ A₁)
--   {σ₀ : Tms Γ₀ Δ₀}{σ₁ : Tms Γ₁ Δ₁}(σ₂ : σ₀ ≡[ Tms≡ Γ₂ Δ₂ ]≡ σ₁)
--   → subT A₀ σ₀ ≡[ Ty≡ Γ₂ ]≡ subT A₁ σ₁
-- []T= = []T=′

-- A[]T= : {Γ Δ : Cxt}{n : ℕ}{A : Ty Δ n}{σ₀ σ₁ : Tms Γ Δ}(σ₂ : σ₀ ≡ σ₁)
--   → subT A σ₀ ≡ subT A σ₁
-- A[]T= σ₂ = []T= refl refl refl σ₂

-- postulate 
  -- π₂β' : ∀{Γ Δ n}{A : Ty Δ n}{δ : Tms Γ Δ}{a : Tm Γ (subT A δ)} → π₂ {Γ} {Δ} {n} {A} (subExt δ a) ≡ a
-- π₂β' = {!TmΓ≡!}

-- π₂β' {A = A} = from≡ (TmΓ= (A[]T= π₁β)) π₂β





-- Tm (Γ , A , B) (subT (subT B ((π₁ id ∘ π₁ id) ↑ A)) (subExt id (◁ ▼)))
-- π₁subext : ∀ {Γ} → π₁ (id {{!!}}) ∘ π₁ (id {{!!}}) ≡ subExt ((π₁ (id {{!!}}) ∘ π₁ (id {{!!}})) ∘ π₁ (id {{!!}})) (π₂ (id {{!!}})) 
-- π₁subext = {!!}


-- argh : ∀{Γ i j} {A : Ty Γ i} {B : Ty (Γ , A) j} {t : Tm Γ {!!}}
--   → subt (subt t (π₁ (id {{!!}}))) (π₁ (id {{!!}}) ∘ π₁ (id {{!!}}))
--   ≡ subt (π₂ (id {{!!}})) (π₁ (id {Γ , A , B}))
-- argh = {!!}

-- postulate
-- -- lemma : ∀{Γ n} {A : Ty Γ n} {t : Tm Γ A} → id ≡ (π₁ id ∘ subExt id t)

--   mmh : ∀{Γ n} {A : Ty Γ n} → Tm Γ A ≡ Tm (Γ , A) (subT A wk)

--   subtwk : ∀{Γ n} {A : Ty Γ n} {t : Tm Γ A} → subt t wk ≡ coe mmh t

-- {-# REWRITE subtwk #-}





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


-- UGLY BUT WAS WORKING:

-- postulate
--   nondepext : ∀{Γ m n} {A : Ty Γ m} {B : Ty Γ n} {a : Tm Γ A} → subT (vsT B) < a > ≡ B
-- -- nondepext = [][]T ◾ cong (subT _) (π₁∘ ◾ (cong π₁ idl ◾ (π₁β ◾ {![id]T!}))) -- ◾ ?
-- {-# REWRITE nondepext #-}



-- postulate
--   π₁ext≡id : ∀{Γ i} {A : Ty Γ i} {a : Tm Γ A} → π₁ id ∘ subExt id a ≡ id
-- -- π₁ext≡id {Γ} {i} {A} {a} = {!!} ◾ {!!}

--   subTsubTsubTsubExtsubExt : ∀{Γ i j} {A : Ty Γ i} {B : Ty Γ j} {a : Tm Γ A} {b : Tm Γ B}
--     → A ≡ subT (subT (subT A (π₁ id)) (π₁ {{!!}} {{!!}} {{!!}} {{!!}} id)) (subExt (subExt id a) b)

--   -- subtsubtExtExt : ∀{Γ i j} {A : Ty Γ i} {B : Ty Γ j} {a : Tm Γ A} {b : Tm Γ B}
--   --   → subt (subt (π₂ id) (π₁ id)) (subExt (subExt id a) b) ≡ coe (TmΓ≡ subTsubTsubTsubExtsubExt) a


-- {-# REWRITE subtsubtExtExt #-}
