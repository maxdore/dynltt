{-# OPTIONS --cubical #-}
module ListPartial where

-- This file contains two definitions of unfold for lists and several examples.
-- Since the unfolds are not necessarily terminating, this file is not marked
-- with --safe

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Base
open import Lemmas
open import Functions
open import List
open import Maybe

private
  variable
    ℓ : Level

module _ {A B : Type ℓ} where
  {-# NON_TERMINATING #-}
  unfold₁ : (B ⊸ Maybe (A × B)) → B ⊸ List A
  unfold₁ f x with f x
  ... | nothing , δ = []○ by oplnothing ∘ δ
  ... | (just (y , x')) , δ = ． y ∷◎ unfold₁ f x' by opl, ∘ opljust ∘ δ

module _ {A B : Type ℓ} where
  map : (A ⊸ B) → List A ⊸ List B
  map f = unfold₁ go where
    go : List A ⊸ Maybe (B × List A)
    go [] = nothing○ by opl[]
    go (z ∷ zs) = just○ ＠ (f z ,◎ ． zs) by opl∷


module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  -- Use with care: the rounds function is not necessarily terminating, but we
  -- need to annotate it as such so that Agda reduces rounds when type-checking
  -- unfold₂ below
  {-# TERMINATING #-}
  rounds : (B → Maybe ((Δ ⊩ A) × B)) → B → ℕ
  rounds f x with f x
  ... | nothing = zero
  ... | just (_ , x') = suc (rounds f x')

module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  {-# NON_TERMINATING #-}
  unfold₂ : (f : B → Maybe ((Δ ⊩ A) × B)) → (x : B) → Δ ^ rounds f x ⊩ List A
  unfold₂ f x with f x
  ... | nothing = []○
  ... | just ((y , δ) , x') = ． y ∷◎ unfold₂ f x' by δ ⊗ᶠ id (Δ ^ rounds f x')


module _ {A : Type} where
  replicate : (m : ℕ) → A -⟨ m ⟩⊸ List A
  replicate m x = unfold₂ go m by prod where
    go : ℕ → Maybe ((ι x ⊩ A) × ℕ)
    go zero = nothing
    go (suc m) = just (． x , m)
    prod : ι x ^ m ⧟ ι x ^ rounds go m
    prod = subst (λ n → ι x ^ m ⧟ ι x ^ n) (mrounds≡m m) (id (ι x ^ m))
      where
      mrounds≡m : (n : ℕ) → n ≡ rounds go n
      mrounds≡m zero = refl
      mrounds≡m (suc m) = cong suc (mrounds≡m m)




