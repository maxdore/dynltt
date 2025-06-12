{-# OPTIONS --cubical --safe -WnoUnsupportedIndexedMatch #-}
module Vector where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec hiding (zipWith)

open import Base
open import Lemmas
open import Functions

private
  variable
    ℓ : Level

module _ {A : Type ℓ} where
  []○ : ◇ ⊩ Vec A 0
  []○ = ． [] by lax[]'

module _ {A : Type ℓ} {n : ℕ} where
  _∷○_ : (A × Vec A n) ⊸ Vec A (suc n)
  _∷○_ (x , xs) = ． (x ∷ xs) by lax∷' ∘ opl,

module _ {A : Type ℓ} {n : ℕ} {Δ₀ Δ₁ : Supply ℓ} where
  _∷◎_ : Δ₀ ⊩ A → Δ₁ ⊩ Vec A n → Δ₀ ⊗ Δ₁ ⊩ Vec A (suc n)
  _∷◎_ = ○→◎ _∷○_


module _ {A B : Type ℓ} where
  zip : {n : ℕ} (xs : Vec A n) → (ys : Vec B n) → ι ys ⊗ ι xs ⊩ Vec (A × B) n
  zip {zero} [] [] = []○ by opl[]' ⊗ᶠ opl[]'
  zip {suc n} (x ∷ xs) (y ∷ ys) = (． x ,◎ ． y) ∷◎ zip xs ys
    by prod
    where
    prod : ι (y ∷ ys) ⊗ ι (x ∷ xs) ⧟ (ι x ⊗ ι y) ⊗ ι ys ⊗ ι xs
    prod =  assoc (ι x ⊗ ι y) (ι ys) (ι xs)
            ∘ (assoc' (ι x) (ι y) (ι ys) ∘ swap (ι y ⊗ ι ys) (ι x)) ⊗ᶠ (id (ι xs))
            ∘ assoc' (ι y ⊗ ι ys) (ι x) (ι xs)
            ∘ opl∷' ⊗ᶠ opl∷'




