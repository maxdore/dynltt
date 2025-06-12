{-# OPTIONS --cubical --safe #-}

-- This file contains linear list constructors, folds and several examples

module List where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr) renaming (length to len)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Base
open import Lemmas
open import Functions


private
  variable
    ℓ : Level


module _ {A : Type ℓ} where
  null : List A → Bool
  null [] = true
  null (x ∷ xs) = false

module _ {A : Type ℓ} where
  []○ : ◇ ⊩ List A
  []○ = ． [] by lax[]

  _∷○_ : A × List A ⊸ List A
  _∷○_ (x , xs) = ． (x ∷ xs) by lax∷ ∘ opl,

module _ {A : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _∷◎_ : Δ₀ ⊩ A → Δ₁ ⊩ List A → Δ₀ ⊗ Δ₁ ⊩ List A
  _∷◎_ = ○→◎ _∷○_
  infixr 5 _∷◎_


-- Version used for typesettting introduction
module IgnoreList {A : Type ℓ} where
  safeHead : (xs : List A) → (y : A) → (if null xs then ι y else ◇) ⊗ ι xs ⊩ A × List A
  safeHead [] y = ． (y , []) by lax,
  safeHead (x ∷ xs) y = ． (x , xs) by lax, ∘ opl∷


module _ {A : Type ℓ} where
  safeHead : (xs : List A) → (y : A) → (if null xs then ι y else ◇) ⊗ ι xs ⊩ A × List A
  safeHead [] y = ． (y , []) by lax,
  safeHead (x ∷ xs) y = ． (x , xs) by lax, ∘ opl∷

module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  foldr₁ : (A × B ⊸ B) → (Δ ⊩ B) → (xs : List A) → Δ ⊗ ι xs ⊩ B
  foldr₁ f z [] = z by unitr Δ ∘ (id Δ) ⊗ᶠ opl[]
  foldr₁ f z (x ∷ xs) = f ＠ (． x ,◎ foldr₁ f z xs) by prod where
    prod : Δ ⊗ ι (x ∷ xs) ⧟ ι x ⊗ Δ ⊗ ι xs
    prod = swap Δ (ι x) ⊗ᶠ (id (ι xs)) ∘ assoc' Δ (ι x) (ι xs) ∘ (id Δ) ⊗ᶠ opl∷

module _ {A : Type ℓ} where
  append : List A × List A ⊸ List A
  append (xs , ys) = foldr₁ _∷○_ (． ys) xs by swap (ι xs) (ι ys) ∘ opl,


module _ {A : Type ℓ} where
  concat : List (List A) ⊸ List A
  concat = foldr₁ append []○


module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  foldr₂ : ((x : A) → (b : B) → ι b ⊗ ι x ⊗ Δ ⊩ B) → ◇ ⊩ B → (xs : List A) → Δ ^ (len xs) ⊗ ι xs ⊩ B
  foldr₂ f z [] = z by opl[]
  foldr₂ f z (x ∷ xs) = f x ＠ foldr₂ f z xs
    by prod where
    prod : (Δ ⊗ Δ ^ len xs) ⊗ ι (x ∷ xs) ⧟ ι x ⊗ Δ ⊗ Δ ^ len xs ⊗ ι xs

    prod = id (ι x) ⊗ᶠ assoc Δ (Δ ^ len xs) (ι xs)
      ∘ swap (Δ ⊗ Δ ^ (len xs)) (ι x) ⊗ᶠ id (ι xs)
      ∘ assoc' (Δ ^ suc (len xs)) (ι x) (ι xs)
      ∘ id (Δ ^ (suc (len xs ))) ⊗ᶠ opl∷


module _ {A : Type ℓ} where
  intersperse : (x : A) (ys : List A) → ι x ^ (len ys) ⊗ ι ys ⊩ List A
  intersperse x = foldr₂ (λ y xys → ． x ∷◎ ． y ∷◎ ． xys by prod y xys) []○ where
    prod : (y : A) (xys : List A) → ι xys ⊗ ι y ⊗ ι x ⧟ ι x ⊗ ι y ⊗ ι xys
    prod y xys = assoc (ι x) (ι y) (ι xys) ∘ swap (ι xys) (ι x ⊗ ι y) ∘ (id (ι xys) ⊗ᶠ swap (ι y) (ι x))


  intersperse' : (x : A) (ys : List A) → ι x ^ predℕ (len ys) ⊗ ι ys ⊩ List A
  intersperse' x [] = ． []
  intersperse' x (y ∷ []) = ． (y ∷ [])
  intersperse' x (y ∷ y' ∷ ys) = ． x ∷◎ ． y ∷◎ intersperse' x (y' ∷ ys)
    by id (ι x) ⊗ᶠ prod
    where
    prod : ι x ^ (len (ys)) ⊗ ι (y ∷ y' ∷ ys) ⧟
        ι y ⊗ ι x ^ (len (ys)) ⊗ ι (y' ∷ ys)
    prod = swap (ι x ^ len ys) (ι y) ⊗ᶠ id (ι (y' ∷ ys)) ∘ assoc' (ι x ^ len ys) (ι y) (ι (y' ∷ ys)) ∘ id (ι x ^ len ys) ⊗ᶠ opl∷ 


module _ {A B : Type ℓ} (m : ℕ) where
  map' :  A -⟨ m ⟩⊸ B → List A -⟨ m ⟩⊸ List B
  map' f [] = []○ by ◇^ m ∘ ⧟^ m opl[]
  map' f (x ∷ xs) = f x ∷◎ map' f xs by ⊗^ m ∘ ⧟^ m opl∷


