{-# OPTIONS --cubical --guardedness #-}
module Conats where

-- This file uses exponentiation with the conatural number type for
-- multiplicites. We turn on Agda's guardedness features since Cubical Agda uses
-- it to construct the conaturals.

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
open import Cubical.Codata.Conat renaming (Conat to ℕ∞ ; Conat′ to ℕ∞')

open import Base

private
  variable
    ℓ : Level


≡to⧟ : {Δ₀ Δ₁ : Supply ℓ} → (Δ₁ ≡ Δ₀) → Δ₀ ⧟ Δ₁
≡to⧟ {Δ₀ = Δ₀} {Δ₁} p = subst (_⧟ Δ₁) p (id Δ₁)

swap : (Δ₀ Δ₁ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⧟ Δ₁ ⊗ Δ₀
swap Δ₀ Δ₁ = ≡to⧟ ((comm-++ Δ₁ Δ₀))


-- Use the functions below with caution---these aren't necessarily terminating,
-- but we have to annotate them as such for the type-checker to reduce an
-- exponentiation with a non-zero number.
{-# TERMINATING #-}
_^_ : Supply ℓ → ℕ∞ → Supply ℓ
{-# TERMINATING #-}
_^'_ : Supply ℓ → ℕ∞' → Supply ℓ

Δ ^ n = Δ ^' force n

Δ ^' zero = ◇
Δ ^' suc n = Δ ⊗ (Δ ^ n)

∞prod : (Δ : Supply ℓ) → (Δ ^ ∞) ⧟ (Δ ⊗ (Δ ^ ∞))

∞prod  Δ = subst (λ a → Δ ^ a ⧟ Δ ^ succ ∞) ∞+1≡∞ (id (Δ ^ (succ ∞)))


{-# NON_TERMINATING #-}
⧟^ : ∀{ℓ}{Δ₀ Δ₁ : Supply ℓ} → (m : ℕ∞) → Δ₀ ⧟ Δ₁ → (Δ₀ ^ m) ⧟ (Δ₁ ^ m)
{-# NON_TERMINATING #-}
⧟^' : ∀{ℓ}{Δ₀ Δ₁ : Supply ℓ} → (m : ℕ∞') → Δ₀ ⧟ Δ₁ → (Δ₀ ^' m) ⧟ (Δ₁ ^' m)

⧟^' zero δ = id ◇
⧟^' (suc m) δ = δ ⊗ᶠ (⧟^ m δ)

⧟^ m δ = ⧟^' (force m) δ

_⊸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⊸ B = (x : A) → ι x ⊩ B

_-⟨_⟩⊸_ : Type ℓ → ℕ∞ → Type ℓ → Type (ℓ-suc ℓ)
A -⟨ m ⟩⊸ B = (x : A) → ι x ^ m ⊩ B

module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _＠_ : ((x : A) → ι x ⊗ Δ₀ ⊩ B) → Δ₁ ⊩ A → Δ₀ ⊗ Δ₁ ⊩ B
  f ＠ (a , δ) = f a by swap Δ₀ (ι a) ∘ id Δ₀ ⊗ᶠ δ

module _ {A B : Type ℓ} {Δ : Supply ℓ} (m : ℕ∞) where
  app : A -⟨ m ⟩⊸ B → Δ ⊩ A → Δ ^ m ⊩ B
  app f (a , δ) = f a by ⧟^ m δ
  syntax app m f x = f ＠⟨ m ⟩ x


module _ {A : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _∷◎_ : Δ₀ ⊩ A → Δ₁ ⊩ List A → Δ₀ ⊗ Δ₁ ⊩ List A
  (x , δ₀) ∷◎ (xs , δ₁) = x ∷ xs , lax∷ ∘ δ₀ ⊗ᶠ δ₁


module _ {A : Type ℓ} where
  {-# NON_TERMINATING #-}
  repeat : A -⟨ ∞ ⟩⊸ List A
  repeat x = ． x ∷◎ repeat x by ∞prod (ι x)


  {-# NON_TERMINATING #-}
  iterate : (A ⊸ A) → A -⟨ ∞ ⟩⊸ List A
  iterate f x = ． x ∷◎ (iterate f ＠⟨ ∞ ⟩ (f ＠ ． x)) by ∞prod (ι x)


