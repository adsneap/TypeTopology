This file defines dyadic rationals, denoted ℤ[1/2], and postulates a
number of operations, relations and properties of the
postulates. These are well known, commonly accepted results, but the
aim is to provide specific implementations of these postulates.

```agda

{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import MLTT.Spartan renaming (_+_ to _∔_) -- TypeTopology

open import Integers.Type
open import Integers.Abs
open import Integers.Addition renaming (_+_ to _+ℤ_)
open import Integers.Multiplication 
open import Integers.Negation 
open import Integers.Order hiding (min₃ ; max₃)
open import Naturals.Addition
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import MLTT.NaturalNumbers
open import Naturals.Properties
open import Notation.Order
open import UF.Base
open import UF.FunExt
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Todd.RationalsDyadic
  (fe : FunExt)
 where
 
open import Todd.TernaryBoehmRealsPrelude

```

Rational dyadics clearly rely on powers of two, so it is useful to
introduce power notation.  Some simple properties of powers are also
proved.

```agda

zero-base : (a : ℕ) → a ℕ^ 0 ＝ 1
zero-base a = refl

raise-again : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ＝ n ℕ^ (a ℕ* b)
raise-again n a zero     = refl
raise-again n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ＝ n ℕ^ (a ℕ* b)
  IH = raise-again n a b
  
  I : n ℕ^ a ℕ^ succ b ＝ n ℕ^ (a ℕ* succ b)
  I = n ℕ^ a ℕ^ succ b        ＝⟨ refl ⟩
      n ℕ^ a ℕ* (n ℕ^ a) ℕ^ b ＝⟨ ap (n ℕ^ a ℕ*_) IH ⟩
      n ℕ^ a ℕ* n ℕ^ (a ℕ* b) ＝⟨ prod-of-powers n a (a ℕ* b) ⟩
      n ℕ^ (a + a ℕ* b)       ＝⟨ refl ⟩
      n ℕ^ (a ℕ* succ b)      ∎

-- TODO : Move following proofs into relevant files/places.

lim₁ : (x : ℤ) → (n : ℕ) → x * pos (2^ (succ n)) ≤ (x * pos 2) * pos (2^ n) 
lim₁ x n = 0 , (x * pos (2^ (succ n))    ＝⟨ ap (x *_) (pos-multiplication-equiv-to-ℕ 2 (2^ n) ⁻¹) ⟩
                x * (pos 2 * pos (2^ n)) ＝⟨ ℤ*-assoc x (pos 2) (pos (2^ n)) ⁻¹ ⟩
                x * pos 2 * pos (2^ n)   ∎)

lim₂ : (x : ℤ) → (n : ℕ) → x * pos (2^ (succ n)) ≤ (x * pos 2 +ℤ pos 1) * pos (2^ n) 
lim₂ x n = ℤ≤-trans _ _ _ (lim₁ x n) (positive-multiplication-preserves-order' _ _ (pos (2^ n)) (power-of-pos-positive n) (≤-incrℤ (x * pos 2)))

lim₃ : (x : ℤ) → (n : ℕ) → x * pos (2^ (succ n)) ≤ (x * pos 2 +ℤ pos 2) * pos (2^ n) 
lim₃ x n = ℤ≤-trans _ _ _ (lim₂ x n) (positive-multiplication-preserves-order' _ _ (pos (2^ n)) (power-of-pos-positive n) (≤-incrℤ (succℤ (x * pos 2))))

```

The definition of dyadic rationals follow.  The dyadic rational ((k ,
δ) , p), to illustrate, refers to the dyadic rational (k / 2ᵟ).  We
could use integers values for δ, but negative values of δ are simply
integer valued dyadic rationals.  For example, (3 / 2⁻⁶) = 192 = (192
/ 2⁰).

```agda

ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ＝ 0) ∔ ((n ≠ 0) × odd z)

ℤ[1/2]-cond-is-prop : (z : ℤ) (n : ℕ) → is-prop ((n ＝ 0) ∔ ((n ≠ 0) × odd z))
ℤ[1/2]-cond-is-prop z n =
 +-is-prop ℕ-is-set (×-is-prop (Π-is-prop (fe 𝓤₀ 𝓤₀) (λ _ → 𝟘-is-prop)) (odd-is-prop z)) λ e (ne , _) → ne e

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

1/2ℤ[1/2] : ℤ[1/2]
1/2ℤ[1/2] = (pos 1 , 1) , inr (positive-not-zero 0 , ⋆)

```

We must now introduce a function to reduce an arbitrary dyadic
rational into it's canonical form (i.e with a positive power
denominator, which is either coprime to an odd denominator or is (2⁰ ＝
1).

As is usual with integers, we split into positive and negative
cases. In the negative case, simply recursively multiply by two to
obtain an integer. In the positive case, we must check if the top is
even or odd, and then recursively divide by two as necessary.

```agda

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise-pos' : (x : ℤ) → (a : ℕ) → let ((k , δ) , p) = normalise-pos x a
                                     in Σ m ꞉ ℕ , ((pos (2^ m) * k , δ + m) ＝ x , a)
normalise-pos' x 0 = 0 , to-×-＝ (ℤ-mult-left-id x) refl
normalise-pos' x (succ a) with even-or-odd? x
... | inr odd-k = 0 , (to-×-＝ (ℤ-mult-left-id x) refl)
... | inl even-k with normalise-pos' (x /2') a
... | (m , e) with from-×-＝' e
... | (e₁ , e₂) = let (k , δ) , p = normalise-pos (x /2') a in
                  succ m ,
                  to-×-＝' (
                  (pos (2^ (succ m)) * k   ＝⟨ refl ⟩
                  pos (2 ℕ* 2^ m) * k      ＝⟨ ap (_* k) (pos-multiplication-equiv-to-ℕ 2 (2^ m) ⁻¹) ⟩
                  pos 2 * pos (2^ m) * k   ＝⟨ ℤ*-assoc (pos 2) (pos (2^ m)) k ⟩
                  pos 2 * (pos (2^ m) * k) ＝⟨ ap (pos 2 *_) e₁ ⟩
                  pos 2 * (x /2')          ＝⟨ ℤ*-comm (pos 2) (x /2') ⟩
                  (x /2') * pos 2          ＝⟨ even-lemma x even-k ⟩ 
                  x ∎)
                  , ap succ e₂)

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

open import Todd.BelowAndAbove

lowest-terms-normalised : (((k , δ) , p) : ℤ[1/2]) → normalise-pos k δ ＝ ((k , δ) , p)
lowest-terms-normalised ((k , .0) , inl refl) = refl
lowest-terms-normalised ((k , zero) , inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
lowest-terms-normalised ((k , succ δ) , inr (δnz , k-odd)) with even-or-odd? k
... | inl k-even = 𝟘-elim (k-even k-odd)
... | inr k-odd = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop z n) refl

normalise-neg' : (x : ℤ) (a : ℕ) → let ((k , δ) , p) = normalise-neg x a
                                   in (k , δ) ＝ pos (2^ (succ a)) * x , 0
normalise-neg' x 0        = to-×-＝ (ℤ*-comm x (pos 2)) refl
normalise-neg' x (succ a) with from-×-＝' (normalise-neg' (x +ℤ x) a)
... | e₁ , e₂ = to-×-＝ I e₂
 where
  I : pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝ pos (2^ (succ (succ a))) * x
  I = pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝⟨ e₁ ⟩
      pos (2^ (succ a)) * (x * pos 2)     ＝⟨ ap (pos (2^ (succ a)) *_) (ℤ*-comm x (pos 2)) ⟩
      pos (2^ (succ a)) * (pos 2 * x)     ＝⟨ ℤ*-assoc (pos (2^ (succ a))) (pos 2) x ⁻¹ ⟩
      pos (2^ (succ a)) * pos 2 * x       ＝⟨ ap (_* x) (pos-multiplication-equiv-to-ℕ (2^ (succ a)) 2) ⟩
      pos (2^ (succ a) ℕ* 2) * x          ＝⟨ ap (λ z → pos z * x) (mult-commutativity (2^ (succ a)) 2) ⟩
      pos (2^ (succ (succ a))) * x ∎

```

Order is easily defined. There are many ways one could define order,
but this definition aligns with the standard definition of order of
rationals.

```agda

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , n) , _) <ℤ[1/2] ((y , m) , _) = x * pos (2^ m) < y * pos (2^ n)
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = x * pos (2^ m) ≤ y * pos (2^ n)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ<-is-prop (x * pos (2^ b)) (y * pos (2^ a)) 

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ≤-is-prop (x * pos (2^ b)) (y * pos (2^ a))

ℤ[1/2]⁺ : 𝓤₀ ̇
ℤ[1/2]⁺ = Σ x ꞉ ℤ[1/2] , 0ℤ[1/2] <ℤ[1/2] x

_<ℤ[1/2]⁺_ _≤ℤ[1/2]⁺_ : ℤ[1/2]⁺ → ℤ[1/2]⁺ → 𝓤₀ ̇
(x , l) <ℤ[1/2]⁺ (y , l') = x <ℤ[1/2] y
(x , l) ≤ℤ[1/2]⁺ (y , l') = x ≤ℤ[1/2] y

is-positive : ℤ[1/2] -> 𝓤₀ ̇
is-positive x = 0ℤ[1/2] <ℤ[1/2] x

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

instance
 Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _≤_ {{Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _≤ℤ[1/2]⁺_

 Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Strict-Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _<_ {{Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _<ℤ[1/2]⁺_

```
The following records define all the properties of dyadic rationals we
need in this development.

```agda

record DyadicProperties : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ＝ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]*-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]*-assoc  : associative _ℤ[1/2]*_
  ℤ[1/2]-negation-involutive : (x : ℤ[1/2]) → x ＝ ℤ[1/2]- (ℤ[1/2]- x)
  ℤ[1/2]-minus-dist : (x y : ℤ[1/2]) → (ℤ[1/2]- (x ℤ[1/2]+ y)) ＝ ((ℤ[1/2]- x) ℤ[1/2]+ (ℤ[1/2]- y))
  min : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  max : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-abs : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-dist : (x y z : ℤ[1/2]) → (x ℤ[1/2]* z) ℤ[1/2]+ (y ℤ[1/2]* z) ＝ ((x ℤ[1/2]+ y) ℤ[1/2]* z)
  
 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

 metric : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 metric p q = ℤ[1/2]-abs (p ℤ[1/2]- q)

 min₃ :  ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 min₃ a b c = min (min a b) c

 min₄ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 min₄ a b c d = min (min₃ a b c) d

 max₃ :  ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 max₃ a b c = max (max a b) c

 max₄ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 max₄ a b c d = max (max₃ a b c) d

 1/2+1/2ℤ[1/2] : 1/2ℤ[1/2] ℤ[1/2]+ 1/2ℤ[1/2] ＝ 1ℤ[1/2]
 1/2+1/2ℤ[1/2] = {!!}

 ℤ[1/2]-mult-left-id : (x : ℤ[1/2]) → 1ℤ[1/2] ℤ[1/2]* x ＝ x
 ℤ[1/2]-mult-left-id = {!!}
 
record OrderProperties : 𝓤₁ ̇ where
 field
  Dp : DyadicProperties
 open DyadicProperties Dp
 field
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  trans' : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
  no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  dense  : (x y : ℤ[1/2]) → (x < y) → Σ k ꞉ ℤ[1/2] , (x < k) × (k < y)
  trans<≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
  ≤-refl : (x : ℤ[1/2]) → x ≤ x
  <-is-≤ℤ[1/2] : (x y : ℤ[1/2]) → x < y → x ≤ y
  diff-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
  diff-positive' : (x y : ℤ[1/2]) → x ≤ y → 0ℤ[1/2] ≤ (y ℤ[1/2]- x)
  <-swap : (x y : ℤ[1/2]) → x < y → (ℤ[1/2]- y) < (ℤ[1/2]- x)
  ≤-swap : (x y : ℤ[1/2]) → x ≤ y → (ℤ[1/2]- y) ≤ (ℤ[1/2]- x)
  ≤-split : (x y : ℤ[1/2]) → x ≤ y → x < y ∔ (x ＝ y)
  <-swap-consequence : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  <-pos-mult : (x y z : ℤ[1/2]) → 0ℤ[1/2] < z → x < y → (x ℤ[1/2]* z) < (y ℤ[1/2]* z)
  <-pos-mult' : (x y : ℤ[1/2]) → 0ℤ[1/2] < x → 0ℤ[1/2] < y → 0ℤ[1/2] < (x ℤ[1/2]* y)

 Bℤ[1/2] : (x y ε : ℤ[1/2]) → 0ℤ[1/2] < ε → 𝓤₀ ̇
 Bℤ[1/2] p q ε l = metric p q < ε

 ℤ[1/2]-minus-zero : 0ℤ[1/2] ＝ (ℤ[1/2]- 0ℤ[1/2])
 ℤ[1/2]-minus-zero = {!!}
 
 ℤ[1/2]<-≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
 ℤ[1/2]<-≤ x y z x<y y≤z with ≤-split y z y≤z
 ... | inl y<z = trans x y z x<y y<z
 ... | inr y=z = transport (x <_) y=z x<y

 ℤ[1/2]≤-< : (x y z : ℤ[1/2]) → x ≤ y → y < z → x < z
 ℤ[1/2]≤-< x y z x≤y y<z with ≤-split x y x≤y
 ... | inl x<y = trans x y z x<y y<z
 ... | inr x＝y = transport (_< z) (x＝y ⁻¹) y<z
 
 trans₂ : (w x y z : ℤ[1/2]) → w < x → x < y → y < z → w < z
 trans₂ w x y z w<x x<y y<z = trans w x z w<x (trans x y z x<y y<z)

 <-swap' : (x y : ℤ[1/2]) → (ℤ[1/2]- x) < (ℤ[1/2]- y) → y < x
 <-swap' x y l = transport₂ _<_ (ℤ[1/2]-negation-involutive y ⁻¹) (ℤ[1/2]-negation-involutive x ⁻¹) (<-swap (ℤ[1/2]- x) (ℤ[1/2]- y) l)

 0<1/2ℤ[1/2] : 0ℤ[1/2] < 1/2ℤ[1/2]
 0<1/2ℤ[1/2] = 0 , refl

 1/2ℤ[1/2]<1ℤ[1/2] : 1/2ℤ[1/2] < 1ℤ[1/2]
 1/2ℤ[1/2]<1ℤ[1/2] = 0 , refl

 0<1ℤ[1/2] : 0ℤ[1/2] < 1ℤ[1/2]
 0<1ℤ[1/2] = 0 , refl

 numerator-≤ : (((a , x) , l₁) ((b , y) , l₂) : ℤ[1/2])
             → x ＝ y → a ≤ b → ((a , x) , l₁) ≤ ((b , y) , l₂)
 numerator-≤ ((a , x) , l₁) ((b , y) , l₂) e l = transport (λ z → a * pos (2^ z) ≤ b * pos (2^ x)) e I
  where
   I : a * pos (2^ x) ≤ b * pos (2^ x)
   I = positive-multiplication-preserves-order' a b (pos (2^ x)) (power-of-pos-positive x) l

 postulate
  ℤ[1/2]<-+ : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → x < (x ℤ[1/2]+ y)
  ℤ[1/2]<-+' : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  ℤ[1/2]<-neg : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → (x ℤ[1/2]- y) < x
  ℤ[1/2]<-neg' : (x y z : ℤ[1/2]) → (x ℤ[1/2]- y) < z → x < (z ℤ[1/2]+ y)
  ℤ[1/2]<-rearrange : (x y z : ℤ[1/2]) → (x ℤ[1/2]+ y) < z → y < (z ℤ[1/2]- x)
  ℤ[1/2]-metric-neg : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε) → metric x y < ε → metric (ℤ[1/2]- x) (ℤ[1/2]- y) < ε
  ℤ[1/2]-pos-abs : (x y : ℤ[1/2]) → x < y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-pos-abs' : (x y : ℤ[1/2]) → x ≤ y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-metric-comm : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε) → Bℤ[1/2] x y ε l → Bℤ[1/2] y x ε l
  ℤ[1/2]≤-adding : (x y u v : ℤ[1/2]) → x ≤ y → u ≤ v → (x ℤ[1/2]+ u) ≤ (y ℤ[1/2]+ v)
  ℤ[1/2]<-adding : (x y u v : ℤ[1/2]) → x < y → u < v → (x ℤ[1/2]+ u) < (y ℤ[1/2]+ v)
  ℤ[1/2]<-+cancel : (x y z : ℤ[1/2]) → (z ℤ[1/2]+ x) < (z ℤ[1/2]+ y) → x < y
  ℤ[1/2]-te : (x y : ℤ[1/2]) → ℤ[1/2]-abs (x ℤ[1/2]+ y) ≤ (ℤ[1/2]-abs x ℤ[1/2]+ ℤ[1/2]-abs y)
  ℤ[1/2]<-to-abs : (x y : ℤ[1/2]) → ((ℤ[1/2]- y) < x) × (x < y) → ℤ[1/2]-abs x < y
  ℤ[1/2]-abs-lemma : (x y : ℤ[1/2]) → ℤ[1/2]-abs (x ℤ[1/2]- y) ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-1/2-< : (x : ℤ[1/2]) → 0ℤ[1/2] < x → (1/2ℤ[1/2] ℤ[1/2]* x) < x
  normalise-< : ((k , p) : ℤ × ℤ) → normalise (k , p) < normalise ((k +pos 2) , p)
  normalise-≤ : ∀ n → ((k , p) : ℤ × ℤ) → normalise (k , p) ≤ normalise ((k +pos n) , p)
  normalise-≤2 : ∀ l r p → l ≤ r → normalise (l , p) ≤ normalise (r , p) 
  normalise-equality : ((k , p) : ℤ × ℤ) → normalise (pos 1 , predℤ p) ＝ normalise (k +pos 2 , p) ℤ[1/2]- normalise (k , p)
  ℤ[1/2]-ordering-property : (a b c d : ℤ[1/2]) → (a ℤ[1/2]- b) < (c ℤ[1/2]- d) → (a < c) ∔ (d < b)
  normalise-succ : (z n : ℤ) → normalise (z , n) ≤ normalise (z +ℤ z , succℤ n)
  normalise-pred' : (z n : ℤ) → normalise (z , predℤ n) ＝ normalise (pos 2 * z , n)
  ℤ[1/2]<-positive-mult : (a b : ℤ[1/2]) → is-positive a → is-positive b → is-positive (a ℤ[1/2]* b)
  ℤ[1/2]-find-lower : ∀ ε → is-positive ε → Σ n ꞉ ℤ , normalise (pos 2 , n) < ε
  normalise-negation : ∀ a b c → normalise (a , c) ℤ[1/2]- normalise (b , c) ＝ normalise (a - b , c)

-- normalise-pos
normalise-≤ : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
            → k * pos (2^ ε) ≤ m * pos (2^ δ)
            → normalise (k , pos δ) ≤ normalise (m , pos ε)
normalise-≤ (k , δ) (m , ε) l with normalise-pos' k δ , normalise-pos' m ε
... | (n₁ , e₁) , (n₂ , e₂) = let (((k' , δ') , p) , ((m' , ε') , p')) = (normalise-pos k δ , normalise-pos m ε) in 
 ℤ≤-ordering-right-cancellable
  (k' * pos (2^ ε'))
   (m' * pos (2^ δ'))
    (pos (2^ (n₁ + n₂)))
     (power-of-pos-positive (n₁ + n₂))
      (transport₂ _≤_ (I k ε k' ε' n₁ n₂ (pr₁ (from-×-＝' e₁) ⁻¹) (pr₂ (from-×-＝' e₂) ⁻¹))
                      ((I m δ m' δ' n₂ n₁ (pr₁ (from-×-＝' e₂) ⁻¹) (pr₂ (from-×-＝' e₁) ⁻¹))
                       ∙ ap (λ z → m' * pos (2^ δ') * pos (2^ z)) (addition-commutativity n₂ n₁)) l)
  where
   k' = pr₁ (pr₁ (normalise-pos k δ))
   δ' = pr₂ (pr₁ (normalise-pos k δ))
   m' = pr₁ (pr₁ (normalise-pos m ε))
   ε' = pr₂ (pr₁ (normalise-pos m ε))
   I : (k : ℤ) (ε : ℕ) (k' : ℤ) (ε' : ℕ) (n₁ n₂ : ℕ) → k ＝ pos (2^ n₁) * k' → ε ＝ ε' + n₂ → k * pos (2^ ε) ＝ k' * pos (2^ ε') * pos (2^ (n₁ + n₂))
   I k ε k' ε' n₁ n₂ e₁ e₂ =
       k * pos (2^ ε)                            ＝⟨ ap (_* pos (2^ ε)) e₁ ⟩
       pos (2^ n₁) * k' * pos (2^ ε)             ＝⟨ ap (_* pos (2^ ε)) (ℤ*-comm (pos (2^ n₁)) k') ⟩
       k' * pos (2^ n₁) * pos (2^ ε)             ＝⟨ ap (λ z → k' * pos (2^ n₁) * pos (2^ z)) e₂ ⟩
       k' * pos (2^ n₁) * pos (2^ (ε' + n₂))    ＝⟨ ℤ*-assoc k' (pos (2^ n₁)) (pos (2^ (ε' + n₂))) ⟩
       k' * (pos (2^ n₁) * pos (2^ (ε' + n₂)))  ＝⟨ ap (k' *_) (pos-multiplication-equiv-to-ℕ (2^ n₁) (2^ (ε' + n₂))) ⟩
       k' * pos ((2^ n₁) ℕ* 2^ (ε' + n₂))       ＝⟨ ap (λ z →  k' * pos ((2^ n₁) ℕ* z)) (prod-of-powers 2 ε' n₂ ⁻¹) ⟩
       k' * pos (2^ n₁ ℕ* (2^ ε' ℕ* 2^ n₂))      ＝⟨ ap (λ z → k' * pos z) (mult-associativity (2^ n₁) (2^ ε') (2^ n₂) ⁻¹) ⟩
       k' * pos (2^ n₁ ℕ* 2^ ε' ℕ* 2^ n₂)        ＝⟨ ap (λ z → k' * pos (z ℕ* 2^ n₂)) (mult-commutativity (2^ n₁) (2^ ε')) ⟩
       k' * pos (2^ ε' ℕ* 2^ n₁ ℕ* 2^ n₂)        ＝⟨ ap (λ z → k' * pos z) (mult-associativity (2^ ε') (2^ n₁) (2^ n₂)) ⟩
       k' * pos (2^ ε' ℕ* (2^ n₁ ℕ* 2^ n₂))      ＝⟨ ap (λ z → k' * z) (pos-multiplication-equiv-to-ℕ (2^ ε') (2^ n₁ ℕ* 2^ n₂) ⁻¹) ⟩
       k' * (pos (2^ ε') * pos (2^ n₁ ℕ* 2^ n₂)) ＝⟨ ap (λ z → k' * (pos (2^ ε') * pos z)) (prod-of-powers 2 n₁ n₂) ⟩
       k' * (pos (2^ ε') * pos (2^ (n₁ + n₂)))  ＝⟨ ℤ*-assoc k' (pos (2^ ε')) (pos (2^ (n₁ + n₂))) ⁻¹ ⟩
       k' * pos (2^ ε') * pos (2^ (n₁ + n₂))    ∎

-- normalise-neg
normalise-≤' : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
            → k * pos (2^ (succ δ)) ≤ m * pos (2^ (succ ε))
            → normalise (k , negsucc δ) ≤ normalise (m , negsucc ε)
normalise-≤' (k , δ) (m , ε) with (from-×-＝' (normalise-neg' k δ) , from-×-＝' (normalise-neg' m ε))
... | ((e₁ , e₂) , e₃ , e₄) = transport₂ _≤_
                               (ℤ*-comm k (pos (2^ (succ δ))) ∙ ap₂ (λ z z' → z * pos (2^ z')) (e₁ ⁻¹) (e₄ ⁻¹))
                                (ℤ*-comm m (pos (2^ (succ ε))) ∙ ap₂ (λ z z' → z * pos (2^ z')) (e₃ ⁻¹) (e₂ ⁻¹))

```

The following code begins the process of directly implementing the
above postulates. They are all commonly accepted results, but time
consuming to prove and so are deferred to a later time.

```agda

_𝔻+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
((k , n) , e) 𝔻+ ((h , m) , e') = normalise ((k * pos m +ℤ h * pos n) , (pos n * pos m))

𝔻+-comm : commutative _𝔻+_
𝔻+-comm ((k , n) , e) ((h , m) , e') = ap normalise (to-×-＝' (I , II)) 
 where
  I : k * pos m +ℤ h * pos n ＝ h * pos n +ℤ k * pos m
  I = ℤ+-comm (k * pos m) (h * pos n)

  II : pos n * pos m ＝ pos m * pos n
  II = ℤ*-comm (pos n) (pos m)
{-
normalise-𝔻+ : ∀ x y → normalise x 𝔻+ normalise y ＝ normalise {!!}
normalise-𝔻+ = {!!}

D+-assoc : associative _𝔻+_
D+-assoc x y z = {!!}
-}
```

The following code may be necessary at some point. Unfortunately,
there was an error in assuming that even and odd numbers are coprime,
so thought is required as to how to define the embedding of dyadic
rationals into rationals.

```agda

open import Notation.CanonicalMap
open import Naturals.Division
open import Rationals.Fractions
open import Rationals.Type
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)

```
Proof that any integer is in lowest terms. 
```agda
zero-denom-lt : (x : ℤ) → is-in-lowest-terms (x , 0)
zero-denom-lt x = (1-divides-all (abs x) , (1 , refl)) , (λ f (k , e) → e)

```
Now we have the inclusion of the dyadic rationals into the rationals,
and the usual canonical map notational.
```agda


--Not ideal, should probably use previously considered method
ℤ[1/2]-to-ℚ' : (a : ℤ) (n : ℕ) → (p : (n ＝ 0) ∔ ¬ (n ＝ 0) × odd a) → ℚ
ℤ[1/2]-to-ℚ' a 0 p        = (a , 0) , (zero-denom-lt a)
ℤ[1/2]-to-ℚ' a (succ n) (inr (nz , a-odd))
 = ℤ[1/2]-to-ℚ' a n (Cases (ℕ-is-discrete n 0) (λ e → inl e) (λ nz → inr (nz , a-odd))) ℚ* 1/2

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((a , n) , p) = ℤ[1/2]-to-ℚ' a n p

instance
 canonical-map-ℤ[1/2]-to-ℚ : Canonical-Map ℤ[1/2] ℚ
 ι {{canonical-map-ℤ[1/2]-to-ℚ}} = ℤ[1/2]-to-ℚ

```



