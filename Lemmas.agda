{-# OPTIONS --cubical --safe #-}
module Lemmas where

-- This file derives some productions using properties of finite multisets, and
-- introduces exponentiation of supplies by some natural number

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)

open import Base


private
  variable
    ℓ : Level

≡to⧟ : {Δ₀ Δ₁ : Supply ℓ} → (Δ₁ ≡ Δ₀) → Δ₀ ⧟ Δ₁
≡to⧟ {Δ₀ = Δ₀} {Δ₁} p = subst (_⧟ Δ₁) p (id Δ₁)

swap : (Δ₀ Δ₁ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⧟ (Δ₁ ⊗ Δ₀)
unitr : (Δ : Supply ℓ) → (Δ ⊗ ◇) ⧟ Δ
assoc' : (Δ₀ Δ₁ Δ₂ : Supply ℓ) → Δ₀ ⊗ (Δ₁ ⊗ Δ₂) ⧟ (Δ₀ ⊗ Δ₁) ⊗ Δ₂

assoc : (Δ₀ Δ₁ Δ₂ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⊗ Δ₂ ⧟ Δ₀ ⊗ Δ₁ ⊗ Δ₂
assoc Δ₀ Δ₁ Δ₂ = ≡to⧟ (assoc-++ Δ₀ Δ₁ Δ₂)

assoc' Δ₀ Δ₁ Δ₂ = ≡to⧟ (sym (assoc-++ Δ₀ Δ₁ Δ₂))


swap Δ₀ Δ₁ = ≡to⧟ ((comm-++ Δ₁ Δ₀))

unitl : (Δ : Supply ℓ) → (◇ ⊗ Δ) ⧟ Δ
unitl Δ = ≡to⧟ refl

unitl' : (Δ : Supply ℓ) → Δ ⧟ (◇ ⊗ Δ)
unitl' Δ = ≡to⧟ refl

unitr Δ = ≡to⧟ (sym (unitr-++ Δ))

unitr' : (Δ : Supply ℓ) → Δ ⧟ Δ ⊗ ◇
unitr' Δ = ≡to⧟ (unitr-++ Δ)


-- We can show that our production type is symmetric

⧟sym : {Δ₀ Δ₁ : Supply ℓ} → Δ₀ ⧟ Δ₁ → Δ₁ ⧟ Δ₀
⧟sym (id Δ₀) = id Δ₀
⧟sym (δ₁ ∘ δ₀) = ⧟sym δ₀ ∘ ⧟sym δ₁
⧟sym  (_⊗ᶠ_ {Δ₀} {Δ₁} {Δ₂} {Δ₃} δ₀ δ₁) = swap Δ₂ Δ₀ ∘ ⧟sym δ₁ ⊗ᶠ ⧟sym δ₀ ∘ swap Δ₁ Δ₃
⧟sym opl, = lax,
⧟sym lax, = opl,
⧟sym opl[] = lax[]
⧟sym lax[] = opl[]
⧟sym opl∷ = lax∷
⧟sym lax∷ = opl∷
⧟sym oplnothing = laxnothing
⧟sym laxnothing = oplnothing
⧟sym opljust = laxjust
⧟sym laxjust = opljust
⧟sym opl[]' = lax[]'
⧟sym lax[]' = opl[]'
⧟sym opl∷' = lax∷'
⧟sym lax∷' = opl∷'



-- The definition of exponentiating some supply with a natural number multiplicity
_^_ : Supply ℓ → ℕ → Supply ℓ
Δ ^ zero = ◇
Δ ^ (suc n) = Δ ⊗ (Δ ^ n)

infixl 50 _^_

-- Some basic lemmas about ^

⧟^ : ∀{ℓ}{Δ₀ Δ₁ : Supply ℓ} → (m : ℕ) → Δ₀ ⧟ Δ₁ → (Δ₀ ^ m) ⧟ (Δ₁ ^ m)
⧟^ zero δ = id ◇
⧟^ (suc m) δ = δ ⊗ᶠ (⧟^ m δ)

◇^ : ∀{ℓ} → (m : ℕ) → _⧟_ {ℓ} (◇ ^ m) ◇
◇^ zero = id _
◇^ (suc m) = unitl ◇ ∘ (id ◇) ⊗ᶠ (◇^ m)

◇^' : ∀{ℓ} → (m : ℕ) → _⧟_ {ℓ} ◇ (◇ ^ m)
◇^' zero = id ◇
◇^' (suc m) = ◇^' m


⊗^ :  ∀{ℓ}{X Y : Supply ℓ} (m : ℕ) → (X ⊗ Y) ^ m ⧟ X ^ m ⊗ Y ^ m
⊗^ zero = unitl' ◇
⊗^ {ℓ} {X} {Y} (suc m) = assoc (X ⊗ X ^ m) Y (Y ^ m)
  ∘ (assoc' X (X ^ m) Y) ⊗ᶠ id (Y ^ m)
  ∘ id X ⊗ᶠ swap Y (X ^ m) ⊗ᶠ id (Y ^ m)
  ∘ (assoc X Y (X ^ m) ⊗ᶠ id (Y ^ m)
  ∘ assoc' (X ⊗ Y) (X ^ m) (Y ^ m)
  ∘ assoc' X Y (X ^ m ⊗ Y ^ m))
  ∘ assoc X Y (X ^ m ⊗ Y ^ m)
  ∘ id (X ⊗ Y) ⊗ᶠ (⊗^ {ℓ} {X} {Y} m)


assoc4 : (X Y Z W : Supply ℓ) → X ⊗ Y ⊗ Z ⊗ W ⧟ (X ⊗ Y ⊗ Z) ⊗ W
assoc4 X Y Z W = assoc X Y Z ⊗ᶠ id W ∘ assoc' (X ⊗ Y) Z W ∘ assoc' X Y (Z ⊗ W)

⊗^' :  ∀{ℓ}{X Y : Supply ℓ} (m : ℕ) → X ^ m ⊗ Y ^ m ⧟ (X ⊗ Y) ^ m
⊗^' zero = id ◇
⊗^' {ℓ} {X} {Y} (suc m) =
  (id (X ⊗ Y) ⊗ᶠ IH)
  ∘ assoc' X Y (X ^ m ⊗ Y ^ m)
  ∘ id X ⊗ᶠ assoc Y (X ^ m) (Y ^ m)
  ∘ assoc X (Y ⊗ X ^ m) (Y ^ m)
  ∘ id X ⊗ᶠ swap (X ^ m) Y ⊗ᶠ id (Y ^ m)
  ∘ assoc4 X (X ^ m) Y (Y ^ m)
  ∘ assoc X (X ^ m) (Y ⊗ Y ^ m)
  where IH = ⊗^' {X = X} {Y} m


exp : (Δ₀ Δ₁ : Supply ℓ) (n : ℕ) → Δ₀ ^ n ⊗ Δ₁ ^ n ⧟ (Δ₀ ⊗ Δ₁) ^ n
exp Δ₀ Δ₁ zero = id ◇
exp X Y (suc n) =
  id (X ⊗ Y) ⊗ᶠ (exp X Y n)
  ∘ assoc' X Y (X ^ n ⊗ Y ^ n)
  ∘ id X ⊗ᶠ assoc Y (X ^ n) (Y ^ n)
  ∘ assoc X (Y ⊗ X ^ n) (Y ^ n)
  ∘ id X ⊗ᶠ swap (X ^ n) (Y) ⊗ᶠ id (Y ^ n)
  ∘ assoc4 X (X ^ n) Y (Y ^ n)
  ∘ assoc X (X ^ n) (Y ⊗ Y ^ n)


expplus : (X : Supply ℓ) (m n : ℕ) → X ^ (m + n) ⧟ X ^ n ⊗ X ^ m
expplus X zero n = unitr' (X ^ n)
expplus X (suc m) n = assoc (X ^ n) X (X ^ m)
  ∘ swap X (X ^ n) ⊗ᶠ id (X ^ m)
  ∘ assoc' X _ _ ∘ id X ⊗ᶠ IH
  where
  IH = expplus X m n

explaw : (X : Supply ℓ) (m n : ℕ) → X ^ (m · n) ⧟ X ^ m ^ n
explaw X zero n = ◇^' n
explaw X (suc m) n =  ⊗^' {X = X} {X ^ m} n
  ∘ swap (X ^ m ^ n) (X ^ n)
  ∘ IH ⊗ᶠ id ( X ^ n )
  ∘ expplus X n (m · n)
  where IH = explaw X m n


