{-# OPTIONS --cubical #-}
module ISort where

-- This file contains a linear implementation of insertion sort

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

open import Base
open import Lemmas
open import Functions
open import List
open import Order


module _ {ℓ : Level} {A : Type ℓ} (_<_ : Rel A A _) (_≟_ : (x y : A) → Ord.compare _<_ x y) where
  open Ord.Total _<_ _≟_

  -- The function below is structurally recursive since the list argument
  -- decreases in each call, but since it is part of a tuple Agda's termination
  -- checker doesn't recognise this fact.
  {-# TERMINATING #-}
  insert : A × List A ⊸ List A
  insert (x , []) =  ． (x ∷ []) by lax∷ ∘ opl,
  insert (x , (y ∷ ys)) with x ≤? y
  ... | inl p = ． (x ∷ y ∷ ys) by lax∷ ∘ opl,
  ... | inr p = ． y ∷◎ insert (x , ys)
    by id (ι y) ⊗ᶠ lax, ∘ swap (ι x) (ι y) ⊗ᶠ id (ι ys) ∘ id (ι x) ⊗ᶠ opl∷ ∘ opl,

  isort : List A ⊸ List A
  isort = foldr₁ insert []○


open NatOrder

-- test that isort does indeed sort
explist : List ℕ
explist = isort _<_ _≟_ (6 ∷ 1 ∷ 23 ∷ 2 ∷ 4 ∷ 12 ∷ 100 ∷ 16 ∷ 31 ∷ []) .fst

test : explist ≡ 1 ∷ 2 ∷ 4 ∷ 6 ∷ 12 ∷ 16 ∷ 23 ∷ 31 ∷ 100 ∷ []
test = refl



