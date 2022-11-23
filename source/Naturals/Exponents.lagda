\begin{code}

{-# OPTIONS --without-K --exact-split --safe  --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Naturals.Addition
open import Naturals.Properties
open import Naturals.Multiplication
open import Naturals.Order
open import UF.Base

module Naturals.Exponents where

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a *_) ^ b) 1

infixl 33 _ℕ^_

2^ : ℕ → ℕ
2^ = 2 ℕ^_

zero-base : (a : ℕ) → a ℕ^ 0 ＝ 1
zero-base a = refl

prod-of-powers : (n a b : ℕ) → (n ℕ^ a) * (n ℕ^ b) ＝ n ℕ^ (a + b)
prod-of-powers n a 0        = refl
prod-of-powers n a (succ b) = I
 where
  I : (n ℕ^ a) * (n ℕ^ succ b) ＝ (n ℕ^ (a + succ b))
  I = (n ℕ^ a) * (n ℕ^ succ b)  ＝⟨ refl                                             ⟩
      (n ℕ^ a) * (n * (n ℕ^ b)) ＝⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹        ⟩
      (n ℕ^ a) * n * (n ℕ^ b)   ＝⟨ ap (_* (n ℕ^ b)) (mult-commutativity (n ℕ^ a) n) ⟩
      n * n ℕ^ a * n ℕ^ b       ＝⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b)           ⟩
      n * (n ℕ^ a * n ℕ^ b)     ＝⟨ ap (n *_) (prod-of-powers n a b)                 ⟩
      n ℕ^ (a + succ b)         ∎

power-of-power : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ＝ n ℕ^ (a * b)
power-of-power n a 0        = refl
power-of-power n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ＝ n ℕ^ (a * b)
  IH = power-of-power n a b
  I : n ℕ^ a ℕ^ succ b ＝ n ℕ^ (a * succ b)
  I = n ℕ^ a ℕ^ succ b       ＝⟨ refl                       ⟩
      n ℕ^ a * (n ℕ^ a) ℕ^ b ＝⟨ ap (n ℕ^ a *_) IH          ⟩
      n ℕ^ a * n ℕ^ (a * b)  ＝⟨ prod-of-powers n a (a * b) ⟩
      n ℕ^ (a + a * b)       ＝⟨ refl                       ⟩
      n ℕ^ (a * succ b)      ∎

exponents-not-zero : (n : ℕ) → ¬ (2^ n ＝ 0)
exponents-not-zero 0        e = positive-not-zero 0 e
exponents-not-zero (succ n) e = exponents-not-zero n (mult-left-cancellable (2^ n) 0 1 e)

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

\end{code}
