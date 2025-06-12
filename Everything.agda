{-# OPTIONS --cubical --guardedness #-}

-- This file contains all code and examples using the encoding of linear logic
-- in Cubical Agda. We have to turn on guardedness as it is used in Conats for
-- the conatural numbers.

-- Note that Axiomatic.agda is also part of the artefact, but not included here
-- since it works in plain Agda (without any libraries).


module Everything where

open import Base
open import Lemmas
open import Functions
open import Maybe
open import List
open import ListPartial
open import Order
open import ISort
open import SSort
open import Conats
open import Vector

