{-# OPTIONS --cubical --safe #-}

-- This file introduces linear functions as special linear judgments.

module Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)

open import Base
open import Lemmas


private
  variable
    ℓ : Level



-- The linear function type:
_⊸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⊸ B = (x : A) → ι x ⊩ B

-- The linear function type with natural number multiplicity:
_-⟨_⟩⊸_ : Type ℓ → ℕ → Type ℓ → Type (ℓ-suc ℓ)
A -⟨ m ⟩⊸ B = (x : A) → ι x ^ m ⊩ B

infixr 0 _-⟨_⟩⊸_
infixr 0 _⊸_

-- Application of linear functions can be defined for dependent linear functions
module Ignore {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _＠_ : ((x : A) → ι x ⊗ Δ₀ ⊩ B x) → ((a , _) : Δ₁ ⊩ A) → Δ₀ ⊗ Δ₁ ⊩ B a
  f ＠ (a , δ) = f a by swap Δ₀ (ι a) ∘ id Δ₀ ⊗ᶠ δ


-- In the paper we also introduce the non-dependent case
module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _＠_ : ((x : A) → ι x ⊗ Δ₀ ⊩ B) → Δ₁ ⊩ A → Δ₀ ⊗ Δ₁ ⊩ B
  f ＠ (a , δ) = f a by swap Δ₀ (ι a) ∘ (id Δ₀ ⊗ᶠ δ)
  infixl -100 _＠_


module _ {A B C : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  ○→◎ : A × B ⊸ C → Δ₀ ⊩ A → Δ₁ ⊩ B → Δ₀ ⊗ Δ₁ ⊩ C
  ○→◎ f (a , δ₀) (b , δ₁) = f ＠ ． (a , b) by lax, ∘ (δ₀ ⊗ᶠ δ₁)

module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _,◎_ : Δ₀ ⊩ A → Δ₁ ⊩ B → Δ₀ ⊗ Δ₁ ⊩ A × B
  _,◎_ = ○→◎ ．


-- As an example, we give these two versions of the same program in the paper:
module _ {A : Type ℓ} {B : Type ℓ} where
  switch : (z : A × B) → ι z ⊩ B × A
  switch (x , y) = ． (y , x) by prod where prod : ι (x , y) ⧟ ι (y , x)
                                           prod = lax, ∘ swap (ι x) (ι y) ∘ opl,

  switch' : A × B ⊸ B × A
  switch' (x , y) = (． y ,◎ ． x) by swap (ι x) (ι y) ∘ opl,



-- Application of a function using some natural number multiplicity
module _ {A B : Type ℓ} {Δ : Supply ℓ} (m : ℕ) where
  app : A -⟨ m ⟩⊸ B → Δ ⊩ A → Δ ^ m ⊩ B
  app f (a , δ) = f a by ⧟^ m δ
  syntax app m f x = f ＠⟨ m ⟩ x

module _ {A : Type ℓ} where
  copy : A -⟨ 2 ⟩⊸ A × A
  copy x = ． (x , x) by lax,


module _ {A B C : Type ℓ} (n m : ℕ) where
  compose : A -⟨ n ⟩⊸ B → B -⟨ m ⟩⊸ C → A -⟨ n · m ⟩⊸ C
  compose f g x = g ＠⟨ m ⟩ (f ＠⟨ n ⟩ ． x) by explaw (ι x) n m


module _ {A : Type ℓ} where
  copytwice : A -⟨ 4 ⟩⊸ (A × A) × (A × A)
  copytwice = compose 2 2 copy copy



