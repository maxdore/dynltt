{-# OPTIONS --cubical --safe #-}

-- This file contains the basic definitions of supplies and productions; as well
-- as the linear derivability type

module Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Vec
open import Cubical.Data.Maybe
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.HITs.FiniteMultiset public hiding ([_]) renaming (FMSet to Bag ; [] to ◇ ; _∷_ to _⨾_ ; _++_ to _⊗_)


Value : (ℓ : Level) → Type (ℓ-suc ℓ)
Value ℓ = Σ[ A ∈ Type ℓ ] A

Supply : (ℓ : Level) → Type (ℓ-suc ℓ)
Supply ℓ = Bag (Value ℓ)

module _ {ℓ : Level}  {A : Type ℓ} where
  ι : A → Supply ℓ
  ι a = (A , a) ⨾ ◇

module _ {ℓ : Level}  where
  infixl 0 _⧟_
  infixl 11 _⊗ᶠ_
  infixl 10 _∘_

  data _⧟_ : Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ) where
    id : ∀ Δ → Δ ⧟ Δ
    _∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ⧟ Δ₂ → Δ₀ ⧟ Δ₁ → Δ₀ ⧟ Δ₂
    _⊗ᶠ_ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ⧟ Δ₁ → Δ₂ ⧟ Δ₃ → (Δ₀ ⊗ Δ₂) ⧟ (Δ₁ ⊗ Δ₃)

    opl, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → ι {A = Σ A B} (a , b) ⧟ (ι a ⊗ ι b)
    lax, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → (ι a ⊗ ι b) ⧟ ι {A = Σ A B} (a , b)

    opl[] : {A : Type ℓ} → (ι {A = List A} []) ⧟ ◇
    lax[] : {A : Type ℓ} → ◇ ⧟ (ι {A = List A} [])
    opl∷ : {A : Type ℓ} {x : A} {xs : List A} → ι (x ∷ xs) ⧟ ι x ⊗ ι xs
    lax∷ : {A : Type ℓ} {x : A} {xs : List A} → ι x ⊗ ι xs ⧟ ι (x ∷ xs)

    oplnothing : {A : Type ℓ} → (ι {A = Maybe A} nothing) ⧟ ◇
    laxnothing : {A : Type ℓ} → ◇ ⧟ (ι {A = Maybe A} nothing)
    opljust : {A : Type ℓ} {x : A} → ι (just x) ⧟ ι x
    laxjust : {A : Type ℓ} {x : A} → ι x ⧟ ι (just x)

    opl[]' : {A : Type ℓ} → (ι {A = Vec A zero} []) ⧟ ◇
    lax[]' : {A : Type ℓ} → ◇ ⧟ (ι {A = Vec A zero} [])
    opl∷' : {n : ℕ} {A : Type ℓ} {x : A} {xs : Vec A n} → ι (x ∷ xs) ⧟ ι x ⊗ ι xs
    lax∷' : {n : ℕ} {A : Type ℓ} {x : A} {xs : Vec A n} → ι x ⊗ ι xs ⧟ ι (x ∷ xs)


private
  variable
    ℓ : Level

_⊩_ : Supply ℓ → Type ℓ → Type (ℓ-suc ℓ)
Δ ⊩ A = Σ[ a ∈ A ] (Δ ⧟ ι a)
infixl -100 _⊩_

module _ {A : Type ℓ} where
  ． : (a : A) → ι a ⊩ A
  ． a = a , id (ι a)

module _ {Δ₀ Δ₁ : Supply ℓ} {A : Type ℓ} where
  _by_ : Δ₀ ⊩ A → (Δ₁ ⧟ Δ₀) → Δ₁ ⊩ A
  (a , δ₂) by  δ₁ = a , δ₂ ∘ δ₁

  infixl -1000 _by_


