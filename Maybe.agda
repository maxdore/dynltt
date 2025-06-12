{-# OPTIONS --cubical --safe #-}
module Maybe where

-- Linear functions for constructors of the maybe type.

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
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
  nothing○ : ◇ ⊩ Maybe A
  nothing○ = ． nothing by laxnothing

  just○ : A ⊸ Maybe A
  just○ x = ． (just x) by laxjust

