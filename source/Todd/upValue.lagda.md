


```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Naturals.Division
open import Naturals.Exponents
open import Naturals.Multiplication
open import Naturals.Order
open import Naturals.Properties
open import UF.Base

module Todd.upValue where

ceilog2-type : 𝓤₀ ̇
ceilog2-type = (n : ℕ) → Σ m ꞉ ℕ , 2 ℕ^ m < (succ (succ n)) × (succ (succ n)) ≤ 2 ℕ^ (succ m)

exponents-of-two-ordered : (m : ℕ) → 2 ℕ^ m < 2 ℕ^ (succ m)
exponents-of-two-ordered 0        = ⋆
exponents-of-two-ordered (succ m) = transport₂ _<_ I II (multiplication-preserves-strict-order (2 ℕ^ m) (2 ℕ^ succ m) 1 IH)
 where 
  IH : 2 ℕ^ m < 2 ℕ^ succ m
  IH = exponents-of-two-ordered m
  I : 2 ℕ^ m * 2 ＝ 2 ℕ^ succ m
  I = mult-commutativity (2 ℕ^ m) 2
  II : 2 ℕ^ succ m * 2 ＝ 2 ℕ^ succ (succ m)
  II = mult-commutativity (2 ℕ^ succ m) 2

-- (ceilog2 n refers to ceiling log2 of (n - 2))
ceilog2 : ceilog2-type
ceilog2 0        = 0 , ⋆ , ⋆
ceilog2 (succ n) with ceilog2 n
... | m , l₁ , l₂ with ≤-split (succ (succ (succ n))) (2 ℕ^ succ m) l₂
... | inl is-less  = m , (<-trans (2 ℕ^ m) (succ (succ n)) (succ (succ (succ n))) l₁ (<-succ n)) , is-less
... | inr is-equal = succ m , I , II
 where
  I : 2 ℕ^ succ m ≤ℕ succ (succ n)
  I = transport (2 ℕ^ succ m ≤_) i (≤-refl (2 ℕ^ (succ m)))
   where
    i : 2 ℕ^ succ m ＝ succ (succ n)
    i = succ-lc is-equal ⁻¹
  II : succ (succ (succ n)) ≤ℕ (2 ℕ^ succ (succ m))
  II = transport (_≤ 2 ℕ^ succ (succ m)) (is-equal ⁻¹) (exponents-of-two-ordered (succ m))

-- fun x = ceil(log2(x+1))

clog2 : ℕ → ℕ
clog2 0 = 0
clog2 (succ n) = succ (pr₁ (ceilog2 n))

open import Integers.Type
open import Integers.Order
open import Integers.Addition

upValue : (a b : ℤ) → a ≤ b → ℕ
upValue a b (n , a≤b) = clog2 (pred (pred n))

```
