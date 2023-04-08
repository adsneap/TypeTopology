Andrew Sneap, 10 March 2022

In this file I define the absolute value for rational numbers,
and prove properties of the absolute value.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Type hiding (abs)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (abs to 𝔽-abs) renaming (-_ to 𝔽-_) hiding (_+_) hiding (_*_)
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Multiplication

module Rationals.Abs where

abs : ℚ → ℚ
abs (q , _) = toℚ (𝔽-abs q)

ℚ-abs-zero : 0ℚ ＝ abs 0ℚ
ℚ-abs-zero = by-definition

toℚ-abs : (q : 𝔽) → abs (toℚ q) ＝ toℚ (𝔽-abs q)
toℚ-abs (x , a) = equiv→equality (𝔽-abs (x' , a')) (𝔽-abs (x , a)) γ
 where
  x'  = numℚ (x , a)
  a'  = dnomℚ (x , a)
  h   = hcf𝔽 (x , a)
  pa  = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'
  ph  = (pos ∘ succ) h

  γ' : ph ℤ* (absℤ x' ℤ* pa) ＝ ph ℤ* (absℤ x ℤ* pa')
  γ' = ph ℤ* (absℤ x' ℤ* pa)    ＝⟨ ℤ*-assoc ph (absℤ x') pa ⁻¹               ⟩
       ph ℤ* absℤ x' ℤ* pa      ＝⟨ refl                                      ⟩
       absℤ ph ℤ* absℤ x' ℤ* pa ＝⟨ ap (_ℤ* pa) (abs-over-mult' ph x' ⁻¹)     ⟩
       absℤ (ph ℤ* x') ℤ* pa    ＝⟨ ap (λ - → absℤ - ℤ* pa) (numr (x , a) ⁻¹) ⟩
       absℤ x ℤ* pa             ＝⟨ ℤ*-comm (absℤ x) pa                       ⟩
       pa ℤ* absℤ x             ＝⟨ ap (_ℤ* absℤ x) (dnomrP' (x , a))         ⟩
       ph ℤ* pa' ℤ* absℤ x      ＝⟨ ℤ*-assoc ph pa' (absℤ x)                  ⟩
       ph ℤ* (pa' ℤ* absℤ x)    ＝⟨ ap (ph ℤ*_) (ℤ*-comm pa' (absℤ x))        ⟩
       ph ℤ* (absℤ x ℤ* pa')    ∎

  γ : 𝔽-abs (x' , a') ≈ 𝔽-abs (x , a)
  γ = ℤ-mult-left-cancellable (absℤ x' ℤ* pa) (absℤ x ℤ* pa') ph id γ'

abs-of-pos-is-pos : (p : ℚ) → 0ℚ ≤ p → abs p ＝ p
abs-of-pos-is-pos ((pos x , a) , α) l = toℚ-to𝔽 ((pos x , a) , α) ⁻¹
abs-of-pos-is-pos ((negsucc x , a) , α) l = 𝟘-elim (ℚ-num-neg-not-pos x a α l)

abs-of-pos-is-pos' : (p : ℚ) → 0ℚ < p → abs p ＝ p
abs-of-pos-is-pos' p l = abs-of-pos-is-pos p (ℚ<-coarser-than-≤ 0ℚ p l)

ℚ-abs-neg-equals-pos : (q : ℚ) → abs q ＝ abs (- q)
ℚ-abs-neg-equals-pos (q , p) = γ
 where
  I : 𝔽-abs q ≈ 𝔽-abs (𝔽- q) → toℚ (𝔽-abs q) ＝ toℚ (𝔽-abs (𝔽- q))
  I = equiv→equality (𝔽-abs q) (𝔽-abs (𝔽- q))

  II : 𝔽-abs q ≈ 𝔽-abs (𝔽- q)
  II = 𝔽-abs-neg-equals-pos q

  γ : abs (q , p) ＝ abs (- (q , p))
  γ = abs (q , p)        ＝⟨ by-definition     ⟩
      toℚ (𝔽-abs q)      ＝⟨ I II              ⟩
      toℚ (𝔽-abs (𝔽- q)) ＝⟨ toℚ-abs (𝔽- q) ⁻¹ ⟩
      abs (toℚ (𝔽- q))   ＝⟨ by-definition     ⟩
      abs (- (q , p))    ∎

ℚ-abs-inverse : (q : ℚ) → (abs q ＝ q) ∔ (abs q ＝ - q)
ℚ-abs-inverse ((pos x , a) , q)     = inl (toℚ-to𝔽 ((pos x , a) , q) ⁻¹)
ℚ-abs-inverse ((negsucc x , a) , q) = inr refl

ℚ-abs-is-positive : (q : ℚ) → 0ℚ ≤ abs q
ℚ-abs-is-positive ((pos zero , a) , _)     = 0 , refl
ℚ-abs-is-positive ((pos (succ x) , a) , q) = γ
 where
  I : 0ℚ < toℚ (pos (succ x) , a)
  I = ℚ-zero-less-than-positive x a

  γ : 0ℚ ≤ abs ((pos (succ x) , a) , q)
  γ = ℚ<-coarser-than-≤ 0ℚ (abs ((pos (succ x) , a) , q)) I
ℚ-abs-is-positive ((negsucc x , a) , q) = γ
 where
  I : 0ℚ < abs ((negsucc x , a) , q)
  I = ℚ-zero-less-than-positive x a

  γ : 0ℚ ≤ abs ((negsucc x , a) , q)
  γ = ℚ<-coarser-than-≤ 0ℚ (abs (((negsucc x , a) , q))) I

ℚ-abs-zero-is-zero : (q : ℚ) → abs q ＝ 0ℚ → q ＝ 0ℚ
ℚ-abs-zero-is-zero ((pos 0 , a) , p) e = γ
 where
  γ : (pos 0 , a) , p ＝ 0ℚ
  γ = numerator-zero-is-zero ((pos 0 , a) , p) refl
ℚ-abs-zero-is-zero ((pos (succ x) , a) , p) e = 𝟘-elim γ
 where
  γ : 𝟘
  γ = ℚ-positive-not-zero x a e
ℚ-abs-zero-is-zero ((negsucc x , a) , p) e = 𝟘-elim (ℚ-positive-not-zero x a e)

ℚ-abs-≤ : (q : ℚ) → (- abs q ≤ q) × (q ≤ abs q)
ℚ-abs-≤ q = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : - abs q ≤ 0ℚ
  II = ℚ≤-swap 0ℚ (abs q) I

  III : - abs q ≤ abs q
  III = ℚ≤-trans (- abs q) 0ℚ (abs q) II I

  γ₁ : abs q ＝ q → (- abs q ≤ q) × (q ≤ abs q)
  γ₁ e = l , r
   where
    l : - abs q ≤ q
    l = transport (- abs q ≤_) e III

    r : q ≤ abs q
    r = transport (q ≤_) (e ⁻¹) (ℚ≤-refl q)

  γ₂ : abs q ＝ - q → (- abs q ≤ q) × (q ≤ abs q)
  γ₂ e = l , r
   where
    IV : q ＝ - abs q
    IV = q       ＝⟨ ℚ-minus-minus q ⟩
         - (- q) ＝⟨ ap -_ (e ⁻¹) ⟩
         - abs q ∎

    l : - abs q ≤ q
    l = transport (_≤ q) IV (ℚ≤-refl q)

    r : q ≤ abs q
    r = transport (_≤ abs q) (IV ⁻¹) III

ℚ≤-to-abs : (x y : ℚ) → (- y ≤ x) × (x ≤ y) → abs x ≤ y
ℚ≤-to-abs x y (l₁ , l₂) = γ (ℚ-abs-inverse x)
 where
  α : - x ≤ - (- y)
  α = ℚ≤-swap (- y) x l₁

  γ : (abs x ＝ x) ∔ (abs x ＝ - x) → abs x ≤ y
  γ (inl l) = transport (_≤ y) (l ⁻¹) l₂
  γ (inr r) = transport₂ _≤_ (r ⁻¹) (ℚ-minus-minus y ⁻¹) α

ℚ<-to-abs : (x y : ℚ) → (- y < x) × (x < y) → abs x < y
ℚ<-to-abs x y (l₁ , l₂) = γ
 where
  I : - y ≤ x
  I = ℚ<-coarser-than-≤ (- y) x l₁

  II : x ≤ y
  II = ℚ<-coarser-than-≤ x y l₂

  III : abs x ≤ y
  III = ℚ≤-to-abs x y (I , II)

  IV : abs x < y → abs x < y
  IV = id

  V : abs x ＝ y → abs x < y
  V e = 𝟘-elim (cases Vγ₁ Vγ₂ (ℚ-abs-inverse x))
   where
    Vγ₁ : ¬ (abs x ＝ x)
    Vγ₁ e' = ℚ<-not-itself x (transport (x <_) (e ⁻¹ ∙ e') l₂)

    Vγ₂ : ¬ (abs x ＝ - x)
    Vγ₂ e' = ℚ<-not-itself x (transport (_< x) VI l₁)
     where
      VI : - y ＝ x
      VI = - y     ＝⟨ ap -_ (e ⁻¹)       ⟩
           - abs x ＝⟨ ap -_ e'           ⟩
           - (- x) ＝⟨ ℚ-minus-minus x ⁻¹ ⟩
           x       ∎

  γ : abs x < y
  γ = cases IV V (ℚ≤-split (abs x) y III)

ℚ-abs-<-unpack :  (q ε : ℚ) → abs q < ε → (- ε < q) × (q < ε)
ℚ-abs-<-unpack q ε o = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : 0ℚ < ε
  II = ℚ≤-<-trans 0ℚ (abs q) ε I o

  III : - ε < 0ℚ
  III = ℚ<-swap 0ℚ ε II

  IV : - ε < abs q
  IV = ℚ<-≤-trans (- ε) 0ℚ (abs q) III I

  γ₁ : abs q ＝ q → (- ε < q) × (q < ε)
  γ₁ e = l , r
   where
    l : - ε < q
    l = transport (- ε <_) e IV

    r : q < ε
    r = transport (_< ε) e o

  γ₂ : abs q ＝ - q → (- ε < q) × (q < ε)
  γ₂ e = l , r
   where
    α : q ＝ - abs q
    α = q       ＝⟨ ℚ-minus-minus q ⟩
        - (- q) ＝⟨ ap -_ (e ⁻¹)    ⟩
        - abs q ∎

    l : - ε < q
    l = transport (- ε <_) (α ⁻¹) (ℚ<-swap (abs q) ε o)

    r : q < ε
    r = ℚ<-swap''' q ε (transport (- ε <_) e IV)

ℚ-abs-≤-unpack : (q ε : ℚ) → abs q ≤ ε → (- ε ≤ q) × (q ≤ ε)
ℚ-abs-≤-unpack q ε l' = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : 0ℚ ≤ ε
  II = ℚ≤-trans 0ℚ (abs q) ε I l'

  III : - ε ≤ 0ℚ
  III = ℚ≤-swap 0ℚ ε II

  IV : - ε ≤ abs q
  IV = ℚ≤-trans (- ε) 0ℚ (abs q) III I

  γ₁ : abs q ＝ q → (- ε ≤ q) × (q ≤ ε)
  γ₁ e = l , r
   where
    l : - ε ≤ q
    l = transport (- ε ≤_) e IV

    r : q ≤ ε
    r = transport (_≤ ε) e l'

  γ₂ : abs q ＝ - q → (- ε ≤ q) × (q ≤ ε)
  γ₂ e = l , r
   where
    α : q ＝ - abs q
    α = q       ＝⟨ ℚ-minus-minus q ⟩
        - (- q) ＝⟨ ap -_ (e ⁻¹)    ⟩
        - abs q ∎

    l : - ε ≤ q
    l = transport (- ε ≤_) (α ⁻¹) (ℚ≤-swap (abs q) ε l')

    r : q ≤ ε
    r = ℚ≤-swap''' q ε (transport (- ε ≤_) e IV)

ℚ-triangle-inequality : (x y : ℚ) → abs (x + y) ≤ abs x + abs y
ℚ-triangle-inequality x y = ℚ≤-to-abs (x + y) (abs x + abs y) (γ I II)
 where
  I : - abs x ≤ x × x ≤ abs x
  I = ℚ-abs-≤ x

  II : - abs y ≤ y × y ≤ abs y
  II = ℚ-abs-≤ y

  γ : - abs x ≤ x × x ≤ abs x
    → - abs y ≤ y × y ≤ abs y
    → - (abs x + abs y) ≤ x + y
    × x + y ≤ abs x + abs y
  γ (l₁ , l₂) (l₃ , l₄) = (transport (_≤ x + y) IV III) , V
   where
    III : (- abs x) - abs y ≤ x + y
    III = ℚ≤-adding (- abs x) x (- abs y) y l₁ l₃

    IV : (- abs x) - abs y ＝ - (abs x + abs y)
    IV = ℚ-minus-dist (abs x) (abs y)

    V : x + y ≤ abs x + abs y
    V = ℚ≤-adding x (abs x) y (abs y) l₂ l₄

pos-abs-no-increase : (q ε : ℚ) → (0ℚ < q) × (q < ε) → abs q < ε
pos-abs-no-increase q ε (l₁ , l₂) = IV
 where
  I : 0ℚ < ε
  I = ℚ<-trans 0ℚ q ε l₁ l₂
  II : - ε < 0ℚ
  II = transport (- ε <_) ℚ-minus-zero-is-zero i
   where
    i : - ε < - 0ℚ
    i = ℚ<-swap 0ℚ ε I
  III : - ε < q
  III = ℚ<-trans (- ε) 0ℚ q II l₁
  IV : abs q < ε
  IV = ℚ<-to-abs q ε (III , l₂)

abs-mult : (x y : ℚ) → abs x * abs y ＝ abs (x * y)
abs-mult x y = case-split (ℚ-dichotomous' x 0ℚ) (ℚ-dichotomous' y 0ℚ)
 where
  case1 : 0ℚ ≤ x → 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  case1 l₁ l₂ = abs x * abs y  ＝⟨ ap (_* abs y) (abs-of-pos-is-pos x l₁)                                         ⟩
                x * abs y      ＝⟨ ap (x *_) (abs-of-pos-is-pos y l₂)                                             ⟩
                x * y          ＝⟨ abs-of-pos-is-pos (x * y) (ℚ≤-pos-multiplication-preserves-order x y l₁ l₂) ⁻¹ ⟩
                abs (x * y)    ∎

  case2 : (0ℚ > x) → (0ℚ > y) → abs x * abs y ＝ abs (x * y)
  case2 l₁ l₂ = goal
   where
    0<-x : 0ℚ < - x
    0<-x = ℚ<-swap'' x l₁
    0<-y : 0ℚ < - y
    0<-y = ℚ<-swap'' y l₂

    remove-negatives : (- x) * (- y) ＝ x * y
    remove-negatives = (- x) * (- y)     ＝⟨ ℚ-negation-dist-over-mult x (- y)        ⟩
                       - x * (- y)       ＝⟨ ap -_ (ℚ*-comm x (- y))                     ⟩
                       - (- y) * x       ＝⟨ ap -_ (ℚ-negation-dist-over-mult y x)    ⟩
                       - (- y * x)       ＝⟨ ℚ-minus-minus (y * x) ⁻¹                 ⟩
                       y * x             ＝⟨ ℚ*-comm y x                                 ⟩
                       x * y             ∎

    0<x*y : 0ℚ < x * y
    0<x*y = transport (0ℚ <_) remove-negatives (ℚ<-pos-multiplication-preserves-order (- x) (- y) 0<-x 0<-y)

    goal : abs x * abs y ＝ abs (x * y)
    goal = abs x * abs y     ＝⟨ ap (_* abs y) (ℚ-abs-neg-equals-pos x)        ⟩
           abs (- x) * abs y ＝⟨ ap (_* abs y) (abs-of-pos-is-pos' (- x) 0<-x) ⟩
           (- x) * abs y     ＝⟨ ap ((- x) *_) (ℚ-abs-neg-equals-pos y)        ⟩
           (- x) * abs (- y) ＝⟨ ap ((- x) *_) (abs-of-pos-is-pos' (- y) 0<-y) ⟩
           (- x) * (- y)     ＝⟨ remove-negatives                                 ⟩
           x * y             ＝⟨ abs-of-pos-is-pos' (x * y) 0<x*y ⁻¹           ⟩
           abs (x * y)       ∎

  case3 : (a b : ℚ) → 0ℚ ≤ a → b < 0ℚ → abs a * abs b ＝ abs (a * b)
  case3 a b l₁ l₂ = abs a * abs b ＝⟨ ap (_* abs b) (abs-of-pos-is-pos a l₁)                   ⟩
                    a * abs b     ＝⟨ ap (a *_) (ℚ-abs-neg-equals-pos b)                       ⟩
                    a * abs (- b) ＝⟨ ap (a *_) (abs-of-pos-is-pos' (- b) (ℚ<-swap'' b l₂)) ⟩
                    a * (- b)     ＝⟨ ℚ*-comm a (- b)                                             ⟩
                    (- b) * a     ＝⟨ ℚ-negation-dist-over-mult b a                            ⟩
                    - b * a       ＝⟨ ap -_ (ℚ*-comm b a)                                         ⟩
                    - a * b       ＝⟨ abs-of-pos-is-pos (- a * b) (ℚ≤-swap' (a * b) I) ⁻¹   ⟩
                    abs (- a * b) ＝⟨ ℚ-abs-neg-equals-pos (a * b) ⁻¹                          ⟩
                    abs (a * b)   ∎

   where
    first : 0ℚ ≤ - b
    first = ℚ≤-swap' b (ℚ<-coarser-than-≤ b 0ℚ l₂)
    second : 0ℚ ≤ a * (- b)
    second = ℚ≤-pos-multiplication-preserves-order a (- b) l₁ first
    third : - (a * (- b)) ≤ - 0ℚ
    third = ℚ≤-swap 0ℚ (a * (- b)) second
    I : a * b ≤ 0ℚ
    I = transport₂ _≤_ II ℚ-minus-zero-is-zero third
     where
      II : - (a * (- b)) ＝ a * b
      II = - a * (- b) ＝⟨ ap -_ (ℚ*-comm a (- b))                     ⟩
           - (- b) * a ＝⟨ ap -_ (ℚ-negation-dist-over-mult b a)    ⟩
           - (- b * a) ＝⟨ ℚ-minus-minus (b * a) ⁻¹                 ⟩
           b * a       ＝⟨ ℚ*-comm b a                                 ⟩
           a * b       ∎

  case-split : x < 0ℚ ∔ 0ℚ ≤ x → y < 0ℚ ∔ 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  case-split (inl l₁) (inl l₂) = case2 l₁ l₂
  case-split (inl l₁) (inr l₂) = goal
   where
    goal : abs x * abs y ＝ abs (x * y)
    goal = abs x * abs y ＝⟨ ℚ*-comm (abs x) (abs y) ⟩
           abs y * abs x ＝⟨ case3 y x l₂ l₁         ⟩
           abs (y * x)   ＝⟨ ap abs (ℚ*-comm y x)    ⟩
           abs (x * y)   ∎
  case-split (inr l₁) (inl l₂) = case3 x y l₁ l₂
  case-split (inr l₁) (inr l₂) = case1 l₁ l₂

\end{code}
