{-# OPTIONS --cubical #-}
module SSort where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sum
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

open import Base
open import Lemmas
open import Functions
open import Maybe
open import List
open import ListPartial
open import Order


private
  variable
    ℓ : Level

module _ {A : Type ℓ} where
  insSnd : A × A × List A ⊸ A × List A
  insSnd (x , y , ys) = ． (y , x ∷ ys) by lax, ∘ id (ι y) ⊗ᶠ lax∷ ∘ swap (ι x) (ι y) ⊗ᶠ id (ι ys) ∘ id (ι x) ⊗ᶠ opl, ∘ opl,

module _ {A : Type ℓ} (_<_ : Rel A A _) (_≟_ : (x y : A) → Ord.compare _<_ x y) where
  open Ord.Total _<_ _≟_

  -- The function below is structurally recursive since the list argument
  -- decreases in each call, but since it is part of a tuple Agda's termination
  -- checker doesn't recognise this fact.
  {-# TERMINATING #-}
  getMin : A × List A ⊸ A × List A
  getMin (x , []) = ． (x , [])
  getMin (x , y ∷ xs) with y ≤? x
  ... | inl p = insSnd ＠ (． x ,◎ getMin (y , xs)) by id (ι x) ⊗ᶠ (lax, ∘ opl∷) ∘ opl,
  ... | inr p = insSnd ＠ (． y ,◎ getMin (x , xs)) by prod
    where prod = id (ι y) ⊗ᶠ lax, ∘ assoc (ι y) (ι x) (ι xs) ∘ swap (ι x) (ι y) ⊗ᶠ id (ι xs) ∘ id (ι x) ⊗ᶠ opl∷ ∘ opl,


  ssort : List A ⊸ List A
  ssort = unfold₁ go where
    go : List A ⊸ Maybe (A × List A)
    go [] = nothing○ by opl[]
    go (x ∷ ys) = just○ ＠ getMin (x , ys) by lax, ∘ opl∷

open NatOrder

-- Normalise test to check that ssort actually sorts.
test : List ℕ
test = ssort _<_ _≟_ (6 ∷ 1 ∷ 23 ∷ 2 ∷ 4 ∷ 12 ∷ 100 ∷ 16 ∷ 31 ∷ []) .fst



