{-# OPTIONS --safe #-}
module Axiomatic where

-- This file contains the basic definitions of supplies and productions in plain
-- Agda (without higher inductive types)


open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
            ; lsuc  to ℓ-suc
            ; _⊔_   to ℓ-max
            ; Set   to Type
            ; Setω  to Typeω )
open import Agda.Builtin.Sigma


data Supply (ℓ : Level) : Type (ℓ-suc ℓ) where
  ◇ : Supply ℓ
  ι : {A : Type ℓ} (a : A) → Supply ℓ
  _⊗_ : Supply ℓ → Supply ℓ → Supply ℓ


infixr 30 _⊗_

module _ {ℓ : Level}  where
  infixl 0 _⧟_
  infixl 11 _⊗ᶠ_
  infixl 10 _∘_

  data _⧟_ : Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ) where
    id : ∀ Δ → Δ ⧟ Δ
    _∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ⧟ Δ₂ → Δ₀ ⧟ Δ₁ → Δ₀ ⧟ Δ₂
    _⊗ᶠ_ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ⧟ Δ₁ → Δ₂ ⧟ Δ₃ → (Δ₀ ⊗ Δ₂) ⧟ (Δ₁ ⊗ Δ₃)
    unitr : ∀ Δ → Δ ⊗ ◇ ⧟ Δ
    unitr' : ∀ Δ → Δ ⧟ Δ ⊗ ◇
    swap : ∀ Δ₀ Δ₁ → Δ₀ ⊗ Δ₁ ⧟ Δ₁ ⊗ Δ₀
    assoc : ∀ Δ₀ Δ₁ Δ₂ → (Δ₀ ⊗ Δ₁) ⊗ Δ₂ ⧟ Δ₀ ⊗ (Δ₁ ⊗ Δ₂)


private
  variable
    ℓ : Level


unitl : ∀ (Δ : Supply ℓ) → ◇ ⊗ Δ ⧟ Δ
unitl Δ = unitr Δ ∘ swap ◇ Δ

unitl' : ∀ (Δ : Supply ℓ) → Δ ⧟ ◇ ⊗ Δ
unitl' Δ = swap Δ ◇ ∘ unitr' Δ

assoc' : ∀ (Δ₀ Δ₁ Δ₂ : Supply ℓ) → Δ₀ ⊗ (Δ₁ ⊗ Δ₂) ⧟ (Δ₀ ⊗ Δ₁) ⊗ Δ₂
assoc' x y z = swap z (x ⊗ y)
               ∘ assoc z x y
               ∘ swap x z ⊗ᶠ id y
               ∘ swap y (x ⊗ z)
               ∘ id y ⊗ᶠ swap z x
               ∘ assoc y z x
               ∘ swap x (y ⊗ z)




