Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Type
open import Dyadics.Negation
open import Dyadics.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_ ; _-_ to _ℤ-_)
open import Integers.Exponentiation
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Naturals.Exponentiation
open import Notation.Order
open import UF.Base hiding (_≈_)

module Dyadics.Addition where

\end{code}

The usual strategy is applied to define addition of dyadic
rationals. We first define addition of unsimplified dyadics, and then
addition of dyadic rationals is defined by normalising the result of
this addition.

\begin{code}

_+'_ : ℤ × ℕ → ℤ × ℕ → ℤ × ℕ
(p , a) +' (q , b) = p * pos (2^ b) ℤ+ q * pos (2^ a) , a ℕ+ b

_+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
(p , _) + (q , _) = normalise-pos (p +' q)

_-_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
p - q = p + (- q)

infixl 32 _+'_
infixl 32 _+_ _-_

\end{code}

Commutativity is trivial as usual, and follows by commutativity of
addition of integers and natural numbers. To get commutativity of
addition of dyadic rationals, we can simply take the action on paths
of normalise-pos on addition of unsimplified dyadic rationals.

\begin{code}

ℤ[1/2]+'-comm : (p q : ℤ × ℕ) → p +' q ＝ q +' p
ℤ[1/2]+'-comm (p , a) (q , b) = ap₂ _,_ I II
 where
  I : p * pos (2^ b) ℤ+ q * pos (2^ a) ＝ q * pos (2^ a) ℤ+ p * pos (2^ b)
  I = ℤ+-comm (p * pos (2^ b)) (q * pos (2^ a))
  II : a ℕ+ b ＝ b ℕ+ a
  II = addition-commutativity a b

ℤ[1/2]+-comm : (p q : ℤ[1/2]) → p + q ＝ q + p
ℤ[1/2]+-comm (p , _) (q , _) = ap normalise-pos (ℤ[1/2]+'-comm p q)

\end{code}

For associativity, it is slightly more involved. It's not possible to
take the action on paths as with commutativity, because on each side
we have two addition, meaning we apply normalise-pos on intermediate
calculations. The idea of the associativity proof is as follows:

(p , α) + (q , β) + (r , γ)
 = normalise-pos p + normalise-pos q + normalise-pos r
 = normalise-pos (p +' q) + normalise-pos r
 = normalise-pos (p +' q +' r)
 = normalise-pos (p +' (q +' r))
 = normalise-pos p + normalise (q +' r)
 = normalise-pos p + (normalise pos q + normalise-pos r)
 = (p , α) + ((q , β) + (r , γ))
 ∎

This proof requires that proof that (p , α) ＝ normalise-pos p, which
is proved in the Dyadics.Type file. It also requires that
(normalise-pos p + normalise-pos q) ＝ (normalise-pos (p +' q)).

This proof follows, preceded by a lemma about equivalences on
unsimplified rationals.

\begin{code}

ℤ[1/2]+'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p +' r) ≈' (q +' r)
ℤ[1/2]+'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p * pos (2^ b) ＝ q * pos (2^ a)
  e' = e
  a' = pos (2^ a)
  b' = pos (2^ b)
  c' = pos (2^ c)

  rearrangement₁ : (a : ℤ) (b c d : ℕ)
   → a * pos (2^ b) * pos (2^ (c ℕ+ d)) ＝ a * pos (2^ c) * pos (2^ (b ℕ+ d))
  rearrangement₁ a b c d = a * b'' * pos (2^ (c ℕ+ d))  ＝⟨ i    ⟩
                           a * b'' * pos (2^ c ℕ* 2^ d) ＝⟨ ii   ⟩
                           a * b'' * (c'' * pos (2^ d)) ＝⟨ iii  ⟩
                           a * b'' * c'' * pos (2^ d)   ＝⟨ iv   ⟩
                           a * (b'' * c'') * pos (2^ d) ＝⟨ v    ⟩
                           a * (c'' * b'') * pos (2^ d) ＝⟨ vi   ⟩
                           a * c'' * b'' * pos (2^ d)   ＝⟨ vii  ⟩
                           a * c'' * (b'' * pos (2^ d)) ＝⟨ viii ⟩
                           a * c'' * pos (2^ b ℕ* 2^ d) ＝⟨ ix   ⟩
                           a * c'' * pos (2^ (b ℕ+ d))  ∎
   where
    b'' = pos (2^ b)
    c'' = pos (2^ c)
    i    = ap (λ - → a * b'' * pos -) (prod-of-powers 2 c d ⁻¹)
    ii   = ap (a * b'' *_) (pos-multiplication-equiv-to-ℕ (2^ c) (2^ d) ⁻¹)
    iii  = ℤ*-assoc (a * b'') (c'') (pos (2^ d)) ⁻¹
    iv   = ap (_* pos (2^ d)) (ℤ*-assoc a b'' (c''))
    v    = ap (λ - → a * - * pos (2^ d)) (ℤ*-comm b'' (c''))
    vi   = ap (_* pos (2^ d)) (ℤ*-assoc a (c'') b'' ⁻¹)
    vii  = ℤ*-assoc (a * c'') b'' (pos (2^ d))
    viii = ap (a * c'' *_) (pos-multiplication-equiv-to-ℕ (2^ b) (2^ d))
    ix   = ap (λ - → a * c'' * pos - ) (prod-of-powers 2 b d)

  I : p * c' * pos (2^ (b ℕ+ c)) ＝ q * c' * pos (2^ (a ℕ+ c))
  I = p * c' * pos (2^ (b ℕ+ c))   ＝⟨ rearrangement₁ p c b c      ⟩
      p * b' * pos (2^ (c ℕ+ c))   ＝⟨ ap (_* pos (2^ (c ℕ+ c))) e ⟩
      q * a' * pos (2^ (c ℕ+ c))   ＝⟨ rearrangement₁ q a c c      ⟩
      q * c' * pos (2^ (a ℕ+ c))   ∎

  γ : (p * c' ℤ+ r * a') * pos (2^ (b ℕ+ c)) -- lhs of unfolded type
    ＝ (q * c' ℤ+ r * b') * pos (2^ (a ℕ+ c)) -- rhs of unfolded type
  γ = (p * c' ℤ+ r * a') * pos (2^ (b ℕ+ c))                   ＝⟨ i   ⟩
      p * c' * pos (2^ (b ℕ+ c)) ℤ+ r * a' * pos (2^ (b ℕ+ c)) ＝⟨ ii  ⟩
      p * c' * pos (2^ (b ℕ+ c)) ℤ+ r * b' * pos (2^ (a ℕ+ c)) ＝⟨ iii ⟩
      q * c' * pos (2^ (a ℕ+ c)) ℤ+ r * b' * pos (2^ (a ℕ+ c)) ＝⟨ iv  ⟩
      (q * c' ℤ+ r * b') * pos (2^ (a ℕ+ c))                   ∎
   where
    i   = distributivity-mult-over-ℤ (p * c') (r * a') (pos (2^ (b ℕ+ c)))
    ii  = ap (p * c' * pos (2^ (b ℕ+ c)) ℤ+_) (rearrangement₁ r a b c)
    iii = ap (_ℤ+ r * b' * pos (2^ (a ℕ+ c))) I
    iv  = distributivity-mult-over-ℤ (q * c') (r * b') (pos (2^ (a ℕ+ c))) ⁻¹

ℤ[1/2]+-normalise-pos : (p q : ℤ × ℕ)
 → normalise-pos (p +' q) ＝ (normalise-pos p) + (normalise-pos q)
ℤ[1/2]+-normalise-pos p q = ≈'-to-＝ (p +' q) (p' +' q') γ
 where
  p' = from-ℤ[1/2] (normalise-pos p)
  q' = from-ℤ[1/2] (normalise-pos q)

  I : p ≈' p'
  I = ≈'-normalise-pos p

  II : q ≈' q'
  II = ≈'-normalise-pos q

  III : (p +' q) ≈' (p' +' q)
  III = ℤ[1/2]+'-≈' p p' q I

  IV : (q +' p') ≈' (q' +' p')
  IV = ℤ[1/2]+'-≈' q q' p' II

  V : (p' +' q) ≈' (p' +' q')
  V = transport₂ _≈'_ (ℤ[1/2]+'-comm q p') (ℤ[1/2]+'-comm q' p') IV

  γ : (p +' q) ≈' (p' +' q')
  γ = ≈'-trans (p +' q) (p' +' q) (p' +' q') III V

ℤ[1/2]+'-assoc : (p q r : ℤ × ℕ) → (p +' q) +' r ＝ p +' (q +' r)
ℤ[1/2]+'-assoc (p , a) (q , b) (r , c) = to-×-＝' (γ₁ , γ₂)
 where
  a' = pos (2^ a)
  b' = pos (2^ b)
  c' = pos (2^ c)

  I : (p * b' ℤ+ q * a') * c' ＝ p * (b' * c') ℤ+ q * c' * a'
  I = (p * b' ℤ+ q * a') * c'      ＝⟨ i   ⟩
      p * b' * c' ℤ+ q * a' * c'   ＝⟨ ii  ⟩
      p * b' * c' ℤ+ q * c' * a'   ＝⟨ iii ⟩
      p * (b' * c') ℤ+ q * c' * a' ∎
   where
    i   = distributivity-mult-over-ℤ (p * b') (q * a') c'
    ii  = ap ( p * b' * c' ℤ+_) (ℤ-mult-rearrangement q a' c')
    iii = ap (_ℤ+ q * c' * a') (ℤ*-assoc p b' c')

  γ₁ : (p * b' ℤ+ q * a') * c' ℤ+ r * pos (2^ (a ℕ+ b))
     ＝ p * pos (2^ (b ℕ+ c)) ℤ+ (q * c' ℤ+ r * b') * a'
  γ₁ = (p * b' ℤ+ q * a') * c' ℤ+ r * pos (2^ (a ℕ+ b))  ＝⟨ i    ⟩
       (p * b' ℤ+ q * a') * c' ℤ+ r * pos (2^ a ℕ* 2^ b) ＝⟨ ii   ⟩
       (p * b' ℤ+ q * a') * c' ℤ+ r * (a' * b')          ＝⟨ iii  ⟩
       p * (b' * c') ℤ+ q * c' * a' ℤ+ r * (a' * b')     ＝⟨ iv   ⟩
       p * (b' * c') ℤ+ q * c' * a' ℤ+ r * (b' * a')     ＝⟨ v    ⟩
       p * (b' * c') ℤ+ q * c' * a' ℤ+ r * b' * a'       ＝⟨ vi   ⟩
       p * (b' * c') ℤ+ (q * c' * a' ℤ+ r * b' * a')     ＝⟨ vii  ⟩
       p * (b' * c') ℤ+ (q * c' ℤ+ r * b') * a'          ＝⟨ viii ⟩
       p * pos (2^ b ℕ* 2^ c) ℤ+ (q * c' ℤ+ r * b') * a' ＝⟨ ix   ⟩
       p * pos (2^ (b ℕ+ c)) ℤ+ (q * c' ℤ+ r * b') * a'  ∎
        where
         iₐₚ : 2^ (a ℕ+ b) ＝ 2^ a ℕ* 2^ b
         iₐₚ = prod-of-powers 2 a b ⁻¹
         iiₐₚ : pos (2^ a ℕ* 2^ b) ＝ pos (2^ a) * pos (2^ b)
         iiₐₚ = pos-multiplication-equiv-to-ℕ (2^ a) (2^ b) ⁻¹
         vₐₚ : r * (b' * a') ＝ r * b' * a'
         vₐₚ = ℤ*-assoc r b' a' ⁻¹
         viiₐₚ : q * c' * a' ℤ+ r * b' * a' ＝ (q * c' ℤ+ r * b') * a'
         viiₐₚ = distributivity-mult-over-ℤ (q * c') (r * b') a' ⁻¹
         viiiₐₚ : pos (2^ b) * pos (2^ c) ＝ pos (2^ b ℕ* 2^ c)
         viiiₐₚ = pos-multiplication-equiv-to-ℕ (2^ b) (2^ c)
         ixₐₚ : 2^ b ℕ* 2^ c ＝ 2 ℕ^ (b ℕ+ c)
         ixₐₚ = prod-of-powers 2 b c

         i    = ap (λ - → (p * b' ℤ+ q * a') * c' ℤ+ r * pos -) iₐₚ
         ii   = ap (λ - → (p * b' ℤ+ q * a') * c' ℤ+ r * -) iiₐₚ
         iii  = ap (λ - → - ℤ+ r * (a' * b')) I
         iv   = ap (λ - → p * (b' * c') ℤ+ q * c' * a' ℤ+ r * -) (ℤ*-comm a' b')
         v    = ap (λ - → p * (b' * c') ℤ+ q * c' * a' ℤ+ -) vₐₚ
         vi   = ℤ+-assoc (p * (b' * c')) ((q * c' * a')) (r * b' * a')
         vii  = ap (λ - → p * (b' * c') ℤ+ -) viiₐₚ
         viii = ap (λ - → p * - ℤ+ (q * c' ℤ+ r * b') * a') viiiₐₚ
         ix   = ap (λ - → p * pos - ℤ+ (q * c' ℤ+ r * b') * a') ixₐₚ

  γ₂ : a ℕ+ b ℕ+ c ＝ a ℕ+ (b ℕ+ c)
  γ₂ = addition-associativity a b c

ℤ[1/2]+-assoc : (p q r : ℤ[1/2]) → p + q + r ＝ p + (q + r)
ℤ[1/2]+-assoc (p , α) (q , β) (r , δ) = γ
 where
  r' : r , δ ＝ normalise-pos r
  r' = ℤ[1/2]-to-normalise-pos (r , δ)
  p' : p , α ＝ normalise-pos p
  p' = ℤ[1/2]-to-normalise-pos (p , α)

  γ : (p , α) + (q , β) + (r , δ) ＝ (p , α) + ((q , β) + (r , δ))
  γ = (p , α) + (q , β) + (r , δ)              ＝⟨ refl ⟩
      normalise-pos (p +' q) + (r , δ)         ＝⟨ i    ⟩
      normalise-pos (p +' q) + normalise-pos r ＝⟨ ii   ⟩
      normalise-pos ((p +' q) +' r)            ＝⟨ iii  ⟩
      normalise-pos (p +' (q +' r))            ＝⟨ iv   ⟩
      normalise-pos p + normalise-pos (q +' r) ＝⟨ v    ⟩
      (p , α) + normalise-pos (q +' r)         ＝⟨ refl ⟩
      (p , α) + ((q , β) + (r , δ)) ∎
   where
    i   = ap (λ - → normalise-pos (p +' q) + -) r'
    ii  = ℤ[1/2]+-normalise-pos (p +' q) r ⁻¹
    iii = ap normalise-pos (ℤ[1/2]+'-assoc p q r)
    iv  = ℤ[1/2]+-normalise-pos p (q +' r)
    v   = ap (_+ normalise-pos (q +' r)) (p' ⁻¹)

ℤ[1/2]'-zero-left-neutral : (p : ℤ × ℕ) → (pos 0 , 0) +' p ＝ p
ℤ[1/2]'-zero-left-neutral (p , a) = ap₂ _,_ γ₁ γ₂
 where
  γ₁ : pos 0 * pos (2^ a) ℤ+ p * pos (2^ 0) ＝ p
  γ₁ = pos 0 * pos (2^ a) ℤ+ p * pos (2^ 0) ＝⟨ i  ⟩
       pos 0 ℤ+ p                           ＝⟨ ii ⟩
       p                                    ∎
   where
    i  = ap (_ℤ+ p * pos (2^ 0)) (ℤ-zero-left-base (pos (2^ a)))
    ii = ℤ-zero-left-neutral p

  γ₂ : 0 ℕ+ a ＝ a
  γ₂ = zero-left-neutral a

ℤ[1/2]-zero-left-neutral : (q : ℤ[1/2]) → 0ℤ[1/2] + q ＝ q
ℤ[1/2]-zero-left-neutral (q , α) = γ
 where
  γ : 0ℤ[1/2] + (q , α) ＝ (q , α)
  γ = 0ℤ[1/2] + (q , α)                 ＝⟨ refl ⟩
      normalise-pos ((pos 0 , 0) +' q)  ＝⟨ i    ⟩
      normalise-pos q                   ＝⟨ ii   ⟩
      (q , α) ∎
   where
    i  = ap normalise-pos (ℤ[1/2]'-zero-left-neutral q)
    ii = ℤ[1/2]-to-normalise-pos (q , α) ⁻¹

ℤ[1/2]-zero-right-neutral : (q : ℤ[1/2]) → q + 0ℤ[1/2] ＝ q
ℤ[1/2]-zero-right-neutral q = γ
 where
  γ : q + 0ℤ[1/2] ＝ q
  γ = q + 0ℤ[1/2] ＝⟨ ℤ[1/2]+-comm 0ℤ[1/2] q ⁻¹  ⟩
      0ℤ[1/2] + q ＝⟨ ℤ[1/2]-zero-left-neutral q ⟩
      q           ∎

ℤ[1/2]-negation-dist : (p q : ℤ[1/2]) → - p + q ＝ (- p) + (- q)
ℤ[1/2]-negation-dist ((p , a) , α) ((q , b) , β) = γ
 where
  a' = pos (2^ a)
  b' = pos (2^ b)

  p' : (p , a) , α ＝ normalise-pos (p , a)
  p' = ℤ[1/2]-to-normalise-pos ((p , a) , α)
  q' : (q , b) , β ＝ normalise-pos (q , b)
  q' = ℤ[1/2]-to-normalise-pos ((q , b) , β)

  γ : - ((p , a) , α) + ((q , b) , β) ＝ (- ((p , a) , α)) + (- ((q , b) , β))
  γ = - ((p , a) , α) + ((q , b) , β)                       ＝⟨ i    ⟩
      - ((p , a) , α) + normalise-pos (q , b)               ＝⟨ ii   ⟩
      - normalise-pos (p , a) + normalise-pos (q , b)       ＝⟨ iii  ⟩
      - normalise-pos ((p , a) +' (q , b))                  ＝⟨ refl ⟩
      - normalise-pos (p * b' ℤ+ q * a' , a ℕ+ b)           ＝⟨ iv   ⟩
      normalise-pos (ℤ- (p * b' ℤ+ q * a') , a ℕ+ b)        ＝⟨ v    ⟩
      normalise-pos ((ℤ- p * b') ℤ+ (ℤ- q * a') , a ℕ+ b)   ＝⟨ vi   ⟩
      normalise-pos ((ℤ- p) * b' ℤ+ (ℤ- q * a') , a ℕ+ b)   ＝⟨ vii  ⟩
      normalise-pos ((ℤ- p) * b' ℤ+ (ℤ- q) * a' , a ℕ+ b)   ＝⟨ refl ⟩
      normalise-pos ((ℤ- p , a) +' (ℤ- q , b))              ＝⟨ viii ⟩
      normalise-pos (ℤ- p , a) + normalise-pos (ℤ- q , b)   ＝⟨ ix   ⟩
      (- normalise-pos (p , a)) + normalise-pos (ℤ- q , b)  ＝⟨ x    ⟩
      (- normalise-pos (p , a)) + (- normalise-pos (q , b)) ＝⟨ xi   ⟩
      (- normalise-pos (p , a)) + (- ((q , b) , β))         ＝⟨ xii  ⟩
      (- ((p , a) , α)) + (- ((q , b) , β))                 ∎
   where
    vₐₚ : ℤ- (p * b' ℤ+ q * a') ＝ (ℤ- p * b') ℤ+ (ℤ- q * a')
    vₐₚ = negation-dist (p * b') (q * a') ⁻¹
    viₐₚ : ℤ- p * b' ＝ (ℤ- p) * b'
    viₐₚ = negation-dist-over-mult' p b' ⁻¹
    viiₐₚ : ℤ- q * a' ＝ (ℤ- q) * a'
    viiₐₚ = negation-dist-over-mult' q a' ⁻¹

    i    = ap (λ z → - ((p , a) , α) + z) q'
    ii   = ap (λ z → - z + normalise-pos (q , b)) p'
    iii  = ap -_ (ℤ[1/2]+-normalise-pos (p , a) (q , b) ⁻¹)
    iv   = minus-normalise-pos (p * b' ℤ+ q * a') (a ℕ+ b)
    v    = ap (λ z → normalise-pos (z , a ℕ+ b)) vₐₚ
    vi   = ap (λ z → normalise-pos (z ℤ+ (ℤ- q * a') , a ℕ+ b)) viₐₚ
    vii  = ap (λ z → normalise-pos ((ℤ- p) * b' ℤ+ z , a ℕ+ b)) viiₐₚ
    viii = ℤ[1/2]+-normalise-pos (ℤ- p , a) (ℤ- q , b)
    ix   = ap (_+ normalise-pos (ℤ- q , b)) (minus-normalise-pos p a ⁻¹)
    x    = ap ((- normalise-pos (p , a)) +_) (minus-normalise-pos q b ⁻¹)
    xi   =  ap (λ z → (- normalise-pos (p , a)) + (- z)) (q' ⁻¹)
    xii  = ap (λ z → (- z) + (- ((q , b) , β))) (p' ⁻¹)

ℤ[1/2]+-inverse-sum-to-zero : (p : ℤ[1/2]) → p - p ＝ 0ℤ[1/2]
ℤ[1/2]+-inverse-sum-to-zero ((p , a) , α) = γ
 where
  a' = pos (2^ a)
  np = normalise-pos (p , a)

  I : p * a' ℤ+ (ℤ- p) * a' ＝ pos 0
  I = p * a' ℤ+ (ℤ- p) * a' ＝⟨ i  ⟩
      p * a' ℤ- p * a'      ＝⟨ ii ⟩
      pos 0                 ∎
   where
    i  = ap (p * a' ℤ+_) (negation-dist-over-mult' p a')
    ii = ℤ-sum-of-inverse-is-zero (p * a')

  II : (p , a) , α ＝ np
  II = ℤ[1/2]-to-normalise-pos ((p , a) , α)

  γ : ((p , a) , α) - ((p , a) , α) ＝ 0ℤ[1/2]
  γ = ((p , a) , α) - ((p , a) , α)                  ＝⟨ i    ⟩
      np - np                                        ＝⟨ ii   ⟩
      np + normalise-pos (ℤ- p , a)                  ＝⟨ iii  ⟩
      normalise-pos ((p , a) +' (ℤ- p , a))          ＝⟨ refl ⟩
      normalise-pos (p * a' ℤ+ (ℤ- p) * a' , a ℕ+ a) ＝⟨ iv   ⟩
      normalise-pos (pos 0 , a ℕ+ a)                 ＝⟨ v    ⟩
      0ℤ[1/2]                                        ∎
   where
    i   = ap₂ _-_ II II
    ii  = ap (np +_) (minus-normalise-pos p a)
    iii = ℤ[1/2]+-normalise-pos (p , a) (ℤ- p , a) ⁻¹
    iv  = ap (λ b → normalise-pos (b , a ℕ+ a)) I
    v   = ℤ[1/2]-numerator-zero-is-zero' (a ℕ+ a)

ℤ[1/2]+-inverse-sum-to-zero' : (p : ℤ[1/2]) → (- p) + p ＝ 0ℤ[1/2]
ℤ[1/2]+-inverse-sum-to-zero' p = γ
 where
  γ : (- p) + p ＝ 0ℤ[1/2]
  γ = (- p) + p ＝⟨ ℤ[1/2]+-comm (- p) p          ⟩
      p - p     ＝⟨ ℤ[1/2]+-inverse-sum-to-zero p ⟩
      0ℤ[1/2]   ∎

\end{code}

Looking towards showing that dyadic rationals are an approximate ordered field,
we can prove the field axiom relating addition with order, with some lemmas
proved first.

\begin{code}

ℤ[1/2]<'-addition-preserves-order : (p q r : ℤ × ℕ)
                                  → p ℤ[1/2]<' q
                                  → p +' r < q +' r
ℤ[1/2]<'-addition-preserves-order (p , a) (q , b) (r , c) l = γ
 where
  pa = pos (2^ a)
  pb = pos (2^ b)
  pc = pos (2^ c)

  I : p * pb * pos (2^ (c ℕ+ c))
    < q * pa * pos (2^ (c ℕ+ c))
  I = positive-multiplication-preserves-order
      (p * pb) (q * pa) (pos (2^ (c ℕ+ c)))
       (exponents-of-two-positive (c ℕ+ c)) l

  II : p * pb * pos (2^ (c ℕ+ c)) ℤ+ r * pa * pb * pc
     < q * pa * pos (2^ (c ℕ+ c)) ℤ+ r * pa * pb * pc
  II = ℤ<-adding'
        (p * pb * pos (2^ (c ℕ+ c)))
        (q * pa * pos (2^ (c ℕ+ c)))
        (r * pa * pb * pc)
        I

  V : (z : ℤ) (d : ℕ) (e : ℕ)
    → z * pos (2^ d) * pos (2^ (c ℕ+ c)) ℤ+ r * pos (2^ e) * pos (2^ d) * pc
    ＝ (z * pc ℤ+ r * (pos (2^ e))) * pos (2^ (d ℕ+ c))
  V z d e = z * pd * pos (2^ (c ℕ+ c)) ℤ+ r * pe * pd * pc  ＝⟨ i    ⟩
            z * pd * pos (2^ c ℕ* 2^ c) ℤ+ r * pe * pd * pc ＝⟨ ii   ⟩
            z * pd * (pc * pc) ℤ+ r * pe * pd * pc          ＝⟨ iii  ⟩
            z * pd * pc * pc ℤ+ r * pe * pd * pc            ＝⟨ iv   ⟩
            (z * pd * pc ℤ+ r * pe * pd) * pc               ＝⟨ v    ⟩
            (z * pc * pd ℤ+ r * pe * pd) * pc               ＝⟨ vi   ⟩
            (z * pc ℤ+ r * pe) * pd * pc                    ＝⟨ vii  ⟩
            (z * pc ℤ+ r * pe) * (pd * pc)                  ＝⟨ viii ⟩
            (z * pc ℤ+ r * pe) * pos (2^ d ℕ* 2^ c)         ＝⟨ ix   ⟩
            (z * pc ℤ+ r * pe) * pos (2^ (d ℕ+ c))          ∎
   where
    pd = pos (2^ d)
    pe = pos (2^ e)

    iᵢ : 2^ (c ℕ+ c) ＝ 2^ c ℕ* 2^ c
    iᵢ = prod-of-powers 2 c c ⁻¹

    iiᵢ : pos (2^ c ℕ* 2^ c) ＝ pc * pc
    iiᵢ = pos-multiplication-equiv-to-ℕ (2^ c) (2^ c) ⁻¹

    viiiᵢ : pd * pc ＝ pos (2^ d ℕ* 2^ c)
    viiiᵢ = pos-multiplication-equiv-to-ℕ (2^ d) (2^ c)

    i    = ap (λ - → z * pd * pos - ℤ+ r * pe * pd * pc) iᵢ
    ii   = ap (λ - → z * pd * - ℤ+ r * pe * pd * pc) iiᵢ
    iii  = ap (_ℤ+ r * pe * pd * pc) (ℤ*-assoc (z * pd) pc pc ⁻¹)
    iv   = distributivity-mult-over-ℤ (z * pd * pc) (r * pe * pd) pc ⁻¹
    v    = ap (λ - → (- ℤ+ r * pe * pd) * pc) (ℤ-mult-rearrangement z pd pc)
    vi   = ap (_* pc) (distributivity-mult-over-ℤ (z * pc) (r * pe) pd ⁻¹)
    vii  = ℤ*-assoc (z * pc ℤ+ r * pe) pd pc
    viii = ap ((z * pc ℤ+ r * pe) *_) viiiᵢ
    ix   = ap (λ - → (z * pc ℤ+ r * pe) * pos -) (prod-of-powers 2 d c)

  III : p * pb * pos (2^ (c ℕ+ c)) ℤ+ r * pa * pb * pc
      ＝ (p * pc ℤ+ r * pa) * pos (2^ (b ℕ+ c))
  III = V p b a

  IV : q * pa * pos (2^ (c ℕ+ c)) ℤ+ r * pa * pb * pc
    ＝ (q * pc ℤ+ r * pb) * pos (2^ (a ℕ+ c))
  IV = q * pa * pos (2^ (c ℕ+ c)) ℤ+ r * pa * pb * pc ＝⟨ i       ⟩
       q * pa * pos (2^ (c ℕ+ c)) ℤ+ r * pb * pa * pc ＝⟨ V q a b ⟩
       (q * pc ℤ+ r * pb) * pos (2^ (a ℕ+ c))         ∎
   where
    iᵢ : r * pa * pb ＝ r * pb * pa
    iᵢ = ℤ-mult-rearrangement r pa pb
    i = ap (λ - → q * pa * pos (2^ (c ℕ+ c)) ℤ+ - * pc) iᵢ

  γ : (p * pc ℤ+ r * pa) * pos (2^ (b ℕ+ c))
    < (q * pc ℤ+ r * pb) * pos (2^ (a ℕ+ c))
  γ = transport₂ _<_ III IV II

ℤ[1/2]<-addition-preserves-order : (p q r : ℤ[1/2])
                                 → p < q
                                 → (p + r) < (q + r)
ℤ[1/2]<-addition-preserves-order (p , α) (q , β) (r , δ) l = γ
 where
  I : p +' r < q +' r
  I = ℤ[1/2]<'-addition-preserves-order p q r l

  γ : normalise-pos (p +' r) < normalise-pos (q +' r)
  γ = normalise-pos-< (p +' r) (q +' r) I

ℤ[1/2]<-addition-preserves-order' : (p q r : ℤ[1/2])
                                  → p < q
                                  → (r + p) < (r + q)
ℤ[1/2]<-addition-preserves-order' p q r l = γ
 where
  I : p + r < q + r
  I = ℤ[1/2]<-addition-preserves-order p q r l

  II : p + r ＝ r + p
  II = ℤ[1/2]+-comm p r

  III : q + r ＝ r + q
  III = ℤ[1/2]+-comm q r

  γ : r + p < r + q
  γ = transport₂ _<_ II III I

ℤ[1/2]≤-addition-preserves-order : (p q r : ℤ[1/2])
                                 → p ≤ q
                                 → (p + r) ≤ (q + r)
ℤ[1/2]≤-addition-preserves-order p q r l = I (ℤ[1/2]≤-split p q l)
 where
  I : p < q ∔ (p ＝ q) → (p + r) ≤ (q + r)
  I (inr e) = transport (λ - → p + r ≤ - + r) e II
   where
    II : p + r ≤ p + r
    II = ℤ[1/2]≤-refl (p + r)
  I (inl l') = ℤ[1/2]<-coarser-than-≤ (p + r) (q + r) II
   where
    II : p + r < q + r
    II = ℤ[1/2]<-addition-preserves-order p q r l'

ℤ[1/2]≤-addition-preserves-order' : (p q r : ℤ[1/2])
                                  → p ≤ q
                                  → (r + p) ≤ (r + q)
ℤ[1/2]≤-addition-preserves-order' p q r l = γ
 where
  I : p + r ≤ q + r
  I = ℤ[1/2]≤-addition-preserves-order p q r l

  II : p + r ＝ r + p
  II = ℤ[1/2]+-comm p r

  III : q + r ＝ r + q
  III = ℤ[1/2]+-comm q r

  γ : r + p ≤ r + q
  γ = transport₂ _≤_ II III I

ℤ[1/2]<-+ : (p q : ℤ[1/2]) → 0ℤ[1/2] < q → p < p + q
ℤ[1/2]<-+ p q l = γ
 where
  I : p + 0ℤ[1/2] < p + q
  I = ℤ[1/2]<-addition-preserves-order' 0ℤ[1/2] q p l

  II : p + 0ℤ[1/2] ＝ p
  II = ℤ[1/2]-zero-right-neutral p

  γ : p < p + q
  γ = transport (_< p + q) II I

ℤ[1/2]<-diff-positive : (p q : ℤ[1/2]) → p < q → 0ℤ[1/2] < q - p
ℤ[1/2]<-diff-positive p q l = γ
 where
  I : p - p < q - p
  I = ℤ[1/2]<-addition-preserves-order p q (- p) l

  II : p - p ＝ 0ℤ[1/2]
  II = ℤ[1/2]+-inverse-sum-to-zero p

  γ : 0ℤ[1/2] < q - p
  γ = transport (_< q - p) II I

ℤ[1/2]-1/2+1/2 : 1/2ℤ[1/2] + 1/2ℤ[1/2] ＝ 1ℤ[1/2]
ℤ[1/2]-1/2+1/2 = refl

\end{code}
