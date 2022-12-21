```agda
{-# OPTIONS --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}
            
open import Integers.Addition renaming (_+_ to _+ℤ_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Notation.Order 
open import UF.Base
open import UF.FunExt
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Todd.Prelude

module Todd.DyadicRationals where
```

This file defines dyadic rationals as a record, along with many widely
accepted operations, relations and results on dyadic rationals. They
are denoted ℤ[1/2].

```
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ＝ 0) + ((n ≠ 0) × odd z)

ℤ[1/2]-cond-is-prop : FunExt → (z : ℤ) (n : ℕ)
                    → is-prop ((n ＝ 0) + ((n ≠ 0) × odd z))
ℤ[1/2]-cond-is-prop fe z n
 = +-is-prop ℕ-is-set
     (×-is-prop (Π-is-prop (fe 𝓤₀ 𝓤₀) (λ _ → 𝟘-is-prop))
                 (odd-is-prop z))
     (λ e (ne , _) → ne e)

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

1/2ℤ[1/2] : ℤ[1/2]
1/2ℤ[1/2] = (pos 1 , 1) , inr (positive-not-zero 0 , ⋆)

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise-pos' : (x : ℤ) → (a : ℕ)
               → let ((k , δ) , p) = normalise-pos x a in
                 Σ m ꞉ ℕ , ((pos (2^ m) ℤ* k , δ +ℕ m) ＝ x , a)
normalise-pos' x 0 = 0 , to-×-＝ (ℤ-mult-left-id x) refl
normalise-pos' x (succ a) with even-or-odd? x
... | inr odd-k = 0 , (to-×-＝ (ℤ-mult-left-id x) refl)
... | inl even-k with normalise-pos' (x /2') a
... | (m , e) with from-×-＝' e
... | (e₁ , e₂)
 = succ m
 , let (k , δ) , p = normalise-pos (x /2') a in
   to-×-＝' (
     (pos (2^ (succ m)) ℤ* k
       ＝⟨ refl ⟩
     pos (2 ℕ* 2^ m) ℤ* k
       ＝⟨ ap (_ℤ* k) (pos-multiplication-equiv-to-ℕ 2 (2^ m) ⁻¹) ⟩
     pos 2 ℤ* pos (2^ m) ℤ* k
       ＝⟨ ℤ*-assoc (pos 2) (pos (2^ m)) k ⟩
     pos 2 ℤ* (pos (2^ m) ℤ* k)
       ＝⟨ ap (pos 2 ℤ*_) e₁ ⟩
     pos 2 ℤ* (x /2')
       ＝⟨ ℤ*-comm (pos 2) (x /2') ⟩
     (x /2') ℤ* pos 2
       ＝⟨ even-lemma x even-k ⟩ 
     x ∎)
    , ap succ e₂
   )

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

normalise-neg' : (x : ℤ) (a : ℕ)
               → let ((k , δ) , p) = normalise-neg x a in
                 (k , δ) ＝ pos (2^ (succ a)) ℤ* x , 0
normalise-neg' x 0        = to-×-＝ (ℤ*-comm x (pos 2)) refl
normalise-neg' x (succ a) with from-×-＝' (normalise-neg' (x +ℤ x) a)
... | e₁ , e₂ = to-×-＝ I e₂
 where
  I : pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝ pos (2^ (succ (succ a))) ℤ* x
  I = pr₁ (pr₁ (normalise-neg (x +ℤ x) a))
        ＝⟨ e₁ ⟩
      pos (2^ (succ a)) ℤ* (x ℤ* pos 2)
        ＝⟨ ap (pos (2^ (succ a)) ℤ*_) (ℤ*-comm x (pos 2)) ⟩
      pos (2^ (succ a)) ℤ* (pos 2 ℤ* x)
        ＝⟨ ℤ*-assoc (pos (2^ (succ a))) (pos 2) x ⁻¹ ⟩
      pos (2^ (succ a)) ℤ* pos 2 ℤ* x
        ＝⟨ ap (_ℤ* x) (pos-multiplication-equiv-to-ℕ (2^ (succ a)) 2) ⟩
      pos (2^ (succ a) ℕ* 2) ℤ* x
        ＝⟨ ap (λ z → pos z ℤ* x) (mult-commutativity (2^ (succ a)) 2) ⟩
      pos (2^ (succ (succ a))) ℤ* x ∎

lowest-terms-normalised : FunExt → (((k , δ) , p) : ℤ[1/2])
                        → normalise-pos k δ ＝ ((k , δ) , p)
lowest-terms-normalised fe ((k , .0) , inl refl) = refl
lowest-terms-normalised fe ((k , zero) , inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
lowest-terms-normalised fe ((k , succ δ) , inr (δnz , k-odd))
 with even-or-odd? k
... | inl k-even = 𝟘-elim (k-even k-odd)
... | inr k-odd = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n) refl

normalise-pos-lemma₁ : FunExt → (k : ℤ) (δ : ℕ)
                     → (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
                     → normalise-pos ((k +ℤ k) /2') δ ＝ (k , δ) , p
normalise-pos-lemma₁ fe k 0 (inl refl)
 = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n)
     (to-×-＝ (div-by-two k) refl)
normalise-pos-lemma₁ fe k 0 (inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
normalise-pos-lemma₁ fe k (succ δ) (inr p) with even-or-odd? ((k +ℤ k) /2')
normalise-pos-lemma₁ fe k (succ δ) (inr (δnz , k-odd)) | inl k-even
 = 𝟘-elim (k-even (transport odd (div-by-two k ⁻¹) k-odd))
... | inr _ = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n)
                (to-×-＝ (div-by-two k) refl)
                
normalise-pos-lemma₂ : (k : ℤ) (δ : ℕ)
                     → normalise-pos k δ ＝ normalise-pos (k +ℤ k) (succ δ)
normalise-pos-lemma₂ k δ with even-or-odd? (k +ℤ k)
... | inl _ = ap (λ s → normalise-pos s δ) (div-by-two k ⁻¹)
... | inr o = 𝟘-elim (times-two-even' k o)

double : ℤ → ℤ
double a = a +ℤ a

normalise-lemma : FunExt → (k : ℤ) (δ : ℕ) (n : ℕ)
                → (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
                → normalise
                    (rec k double n +ℤ rec k double n , (pos (succ δ) +ℤ pos n))
                ＝ (k , δ) , p
normalise-lemma fe k δ 0 p with even-or-odd? (k +ℤ k)
... | inl even = normalise-pos-lemma₁ fe k δ p
... | inr odd = 𝟘-elim (times-two-even' k odd)
normalise-lemma fe k δ (succ n) p with even-or-odd? (k +ℤ k)
... | inl even
 = let y = rec k double n 
       z = (y +ℤ y) in 
   normalise (z +ℤ z , (succℤ (pos (succ δ) +ℤ pos n)))
     ＝⟨ ap (λ - → normalise (z +ℤ z , succℤ -))
           (distributivity-pos-addition (succ δ) n) ⟩
   normalise (z +ℤ z , succℤ (pos (succ δ +ℕ n)))
     ＝⟨ refl ⟩
   normalise-pos (z +ℤ z) (succ (succ δ +ℕ n))
     ＝⟨ normalise-pos-lemma₂ z (succ δ +ℕ n) ⁻¹ ⟩
   normalise-pos z (succ δ +ℕ n)
     ＝⟨ refl ⟩
   normalise (z , pos (succ δ +ℕ n))
     ＝⟨ ap (λ - → normalise (z , -))
           (distributivity-pos-addition (succ δ) n ⁻¹) ⟩
   normalise (z , pos (succ δ) +ℤ pos n)
     ＝⟨ normalise-lemma fe k δ n p ⟩
   (k , δ) , p ∎ 
... | inr odd = 𝟘-elim (times-two-even' k odd)

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , n) , _) <ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) < y ℤ* pos (2^ n)
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) ≤ y ℤ* pos (2^ n)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _)
 = ℤ<-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a)) 

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _)
 = ℤ≤-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a))

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

record Dyadics : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  -- ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  -- ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]

 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

 field
  -- ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ＝ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  -- ℤ[1/2]*-comm   : commutative _ℤ[1/2]*_
  -- ℤ[1/2]*-assoc  : associative _ℤ[1/2]*_
  -- ℤ[1/2]-mult-left-id : (x : ℤ[1/2]) → 1ℤ[1/2] ℤ[1/2]* x ＝ x
  -- ℤ[1/2]-negation-involutive : (x : ℤ[1/2]) → x ＝ ℤ[1/2]- (ℤ[1/2]- x)
  {- ℤ[1/2]-minus-dist
   : (x y : ℤ[1/2])
   → (ℤ[1/2]- (x ℤ[1/2]+ y))＝ ((ℤ[1/2]- x) ℤ[1/2]+ (ℤ[1/2]- y)) -}
  -- min : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  -- max : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-abs : ℤ[1/2] → ℤ[1/2]
  {- ℤ[1/2]-dist
   : (x y z : ℤ[1/2])
   → (x ℤ[1/2]* z) ℤ[1/2]+ (y ℤ[1/2]* z) ＝ ((x ℤ[1/2]+ y) ℤ[1/2]* z) -}
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  trans' : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
  -- no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  -- no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  dense  : (x y : ℤ[1/2]) → (x < y) → Σ k ꞉ ℤ[1/2] , (x < k) × (k < y)
  -- trans<≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
  ≤-refl : (x : ℤ[1/2]) → x ≤ x
  <-is-≤ℤ[1/2] : (x y : ℤ[1/2]) → x < y → x ≤ y
  diff-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
  -- diff-positive' : (x y : ℤ[1/2]) → x ≤ y → 0ℤ[1/2] ≤ (y ℤ[1/2]- x)
  <-swap : (x y : ℤ[1/2]) → x < y → (ℤ[1/2]- y) < (ℤ[1/2]- x)
  ≤-swap : (x y : ℤ[1/2]) → x ≤ y → (ℤ[1/2]- y) ≤ (ℤ[1/2]- x)
  ≤-swap' : (x y : ℤ[1/2]) → (ℤ[1/2]- x) ≤ (ℤ[1/2]- y) → y ≤ x
  ≤-split : (x y : ℤ[1/2]) → x ≤ y → x < y + (x ＝ y)
  -- <-swap-consequence : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  {- <-pos-mult
   : (x y z : ℤ[1/2]) → 0ℤ[1/2] < z
   → x < y → (x ℤ[1/2]* z) < (y ℤ[1/2]* z) -}
  <-pos-mult'
   : (x y : ℤ[1/2]) → 0ℤ[1/2] < x
   → 0ℤ[1/2] < y → 0ℤ[1/2] < (x ℤ[1/2]* y)
  -- ℤ[1/2]-minus-zero : 0ℤ[1/2] ＝ (ℤ[1/2]- 0ℤ[1/2])
  ℤ[1/2]<-+ : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → x < (x ℤ[1/2]+ y)
  -- ℤ[1/2]<-+' : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  ℤ[1/2]<-neg : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → (x ℤ[1/2]- y) < x
  -- ℤ[1/2]<-neg' : (x y z : ℤ[1/2]) → (x ℤ[1/2]- y) < z → x < (z ℤ[1/2]+ y)
  ℤ[1/2]<-rearrange : (x y z : ℤ[1/2]) → (x ℤ[1/2]+ y) < z → y < (z ℤ[1/2]- x)
  -- ℤ[1/2]-pos-abs
  -- : (x y : ℤ[1/2]) → x < y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  -- ℤ[1/2]-pos-abs'
  -- : (x y : ℤ[1/2]) → x ≤ y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  -- ℤ[1/2]≤-adding
  --  : (x y u v : ℤ[1/2]) → x ≤ y → u ≤ v → (x ℤ[1/2]+ u) ≤ (y ℤ[1/2]+ v)
  -- ℤ[1/2]<-adding
  -- : (x y u v : ℤ[1/2]) → x < y → u < v → (x ℤ[1/2]+ u) < (y ℤ[1/2]+ v)
  -- ℤ[1/2]<-+cancel
  --  : (x y z : ℤ[1/2]) → (z ℤ[1/2]+ x) < (z ℤ[1/2]+ y) → x < y
  -- ℤ[1/2]-te
  -- : (x y : ℤ[1/2])
  -- → ℤ[1/2]-abs (x ℤ[1/2]+ y) ≤ (ℤ[1/2]-abs x ℤ[1/2]+ ℤ[1/2]-abs y)
  -- ℤ[1/2]<-to-abs
  --  : (x y : ℤ[1/2]) → ((ℤ[1/2]- y) < x) × (x < y) → ℤ[1/2]-abs x < y
  -- ℤ[1/2]-abs-lemma
  -- : (x y : ℤ[1/2]) → ℤ[1/2]-abs (x ℤ[1/2]- y) ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-1/2-< : (x : ℤ[1/2]) → 0ℤ[1/2] < x → (1/2ℤ[1/2] ℤ[1/2]* x) < x
  {- normalise-<
   : ((k , p) : ℤ × ℤ)
   → normalise (k , p) < normalise ((k +pos 2) , p) -}
  normalise-≤
   : (n : ℕ) → ((k , p) : ℤ × ℤ)
   → normalise (k , p) ≤ normalise ((k +pos n) , p)
  
  {- normalise-equality : ((k , p) : ℤ × ℤ)
                     → normalise (pos 1 , predℤ p)
                     ＝ normalise (k +pos 2 , p) ℤ[1/2]- normalise (k , p) -}
  ℤ[1/2]-ordering-property
   : (a b c d : ℤ[1/2]) → (a ℤ[1/2]- b) < (c ℤ[1/2]- d) → (a < c) + (d < b)
  {-
  normalise-succ : (z n : ℤ) → normalise (z , n) ≤ normalise (z +ℤ z , succℤ n) -}
  normalise-succ' : (z n : ℤ) → normalise (z , n)
                              ＝ normalise (z +ℤ z , succℤ n)
  normalise-pred' : (z n : ℤ) → normalise (z , predℤ n)
                              ＝ normalise (pos 2 ℤ* z , n)
  ℤ[1/2]<-positive-mult
   : (a b : ℤ[1/2]) → is-positive a → is-positive b → is-positive (a ℤ[1/2]* b)
  ℤ[1/2]-find-lower : (ε : ℤ[1/2]) → is-positive ε
                    → Σ n ꞉ ℤ , normalise (pos 2 , n) < ε
  
  normalise-negation
   : (a b c : ℤ)
   → normalise (a , c) ℤ[1/2]- normalise (b , c) ＝ normalise (a ℤ- b , c)
  normalise-negation' : (a b : ℤ)
                      → ℤ[1/2]- normalise (a , b) ＝ normalise (ℤ- a , b)
  from-normalise-≤-same-denom
   : (a b c : ℤ) → normalise (a , c) ≤ normalise (b , c) → a ≤ b
   {-
 metric : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 metric p q = ℤ[1/2]-abs (p ℤ[1/2]- q)

 Bℤ[1/2] : (x y ε : ℤ[1/2]) → 0ℤ[1/2] < ε → 𝓤₀ ̇
 Bℤ[1/2] p q ε l = metric p q < ε
 -}
{-
 field
  ℤ[1/2]-metric-neg : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε)
                    → metric x y < ε → metric (ℤ[1/2]- x) (ℤ[1/2]- y) < ε
  ℤ[1/2]-metric-comm : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε)
                    → Bℤ[1/2] x y ε l → Bℤ[1/2] y x ε l
-}
 ℤ[1/2]<-≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
 ℤ[1/2]<-≤ x y z x<y y≤z with ≤-split y z y≤z
 ... | inl y<z = trans x y z x<y y<z
 ... | inr y=z = transport (x <_) y=z x<y

 ℤ[1/2]≤-< : (x y z : ℤ[1/2]) → x ≤ y → y < z → x < z
 ℤ[1/2]≤-< x y z x≤y y<z with ≤-split x y x≤y
 ... | inl x<y = trans x y z x<y y<z
 ... | inr x＝y = transport (_< z) (x＝y ⁻¹) y<z
{-
 trans₂ : (w x y z : ℤ[1/2]) → w < x → x < y → y < z → w < z
 trans₂ w x y z w<x x<y y<z = trans w x z w<x (trans x y z x<y y<z)

 <-swap' : (x y : ℤ[1/2]) → (ℤ[1/2]- x) < (ℤ[1/2]- y) → y < x
 <-swap' x y l
  = transport₂ _<_ (ℤ[1/2]-negation-involutive y ⁻¹)
      (ℤ[1/2]-negation-involutive x ⁻¹) (<-swap (ℤ[1/2]- x) (ℤ[1/2]- y) l)
-}
 0<1/2ℤ[1/2] : 0ℤ[1/2] < 1/2ℤ[1/2]
 0<1/2ℤ[1/2] = 0 , refl
{-
 1/2ℤ[1/2]<1ℤ[1/2] : 1/2ℤ[1/2] < 1ℤ[1/2]
 1/2ℤ[1/2]<1ℤ[1/2] = 0 , refl
-}
 0<1ℤ[1/2] : 0ℤ[1/2] < 1ℤ[1/2]
 0<1ℤ[1/2] = 0 , refl

 normalise-≤2 : (l r p : ℤ) → l ≤ r → normalise (l , p) ≤ normalise (r , p)
 normalise-≤2 l r p (j , refl) = normalise-≤ j (l , p)
 {-
 numerator-≤ : (((a , x) , l₁) ((b , y) , l₂) : ℤ[1/2])
             → x ＝ y → a ≤ b → ((a , x) , l₁) ≤ ((b , y) , l₂)
 numerator-≤ ((a , x) , l₁) ((b , y) , l₂) e l
  = transport (λ z → a ℤ* pos (2^ z) ≤ b ℤ* pos (2^ x)) e I
  where
   I : a ℤ* pos (2^ x) ≤ b ℤ* pos (2^ x)
   I = positive-multiplication-preserves-order' a b (pos (2^ x))
         (power-of-pos-positive x) l

 numerator-≤' : (((a , x) , l₁) ((b , y) , l₂) : ℤ[1/2])
              → x ＝ y
              → ((a , x) , l₁) ≤ ((b , y) , l₂)
              → a ≤ b
 numerator-≤'((a , x) , l₁) ((b , y) , l₂) e l
  = ℤ≤-ordering-right-cancellable a b (pos (2^ x))
         (power-of-pos-positive x) I
  where
   I : a ℤ* pos (2^ x) ≤ b ℤ* pos (2^ x)
   I = transport (λ z → a ℤ* pos (2^ z) ≤ b ℤ* pos (2^ x)) (e ⁻¹) l
 
 normalise-≤' : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
             → k ℤ* pos (2^ ε) ≤ m ℤ* pos (2^ δ)
             → normalise (k , pos δ) ≤ normalise (m , pos ε)
 normalise-≤' (k , δ) (m , ε) l with normalise-pos' k δ , normalise-pos' m ε
 ... | (n₁ , e₁) , (n₂ , e₂)
  = let ((k' , δ') , p)  = normalise-pos k δ
        ((m' , ε') , p') = normalise-pos m ε in 
   ℤ≤-ordering-right-cancellable
    (k' ℤ* pos (2^ ε'))
     (m' ℤ* pos (2^ δ'))
      (pos (2^ (n₁ +ℕ n₂)))
       (power-of-pos-positive (n₁ +ℕ n₂))
        (transport₂ _≤_
          (I k ε k' ε' n₁ n₂ (pr₁ (from-×-＝' e₁) ⁻¹) (pr₂ (from-×-＝' e₂) ⁻¹))
          ((I m δ m' δ' n₂ n₁ (pr₁ (from-×-＝' e₂) ⁻¹) (pr₂ (from-×-＝' e₁) ⁻¹))
           ∙ ap (λ z → m' ℤ* pos (2^ δ') ℤ* pos (2^ z))
               (addition-commutativity n₂ n₁)) l)
   where
    k' = pr₁ (pr₁ (normalise-pos k δ))
    δ' = pr₂ (pr₁ (normalise-pos k δ))
    m' = pr₁ (pr₁ (normalise-pos m ε))
    ε' = pr₂ (pr₁ (normalise-pos m ε))
    I : (k : ℤ) (ε : ℕ) (k' : ℤ) (ε' : ℕ) (n₁ n₂ : ℕ)
      → k ＝ pos (2^ n₁) ℤ* k' → ε ＝ ε' +ℕ n₂
      → k ℤ* pos (2^ ε) ＝ k' ℤ* pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂))
    I k ε k' ε' n₁ n₂ e₁ e₂
     = k ℤ* pos (2^ ε)
         ＝⟨ ap (_ℤ* pos (2^ ε)) e₁ ⟩
       pos (2^ n₁) ℤ* k' ℤ* pos (2^ ε)
         ＝⟨ ap (_ℤ* pos (2^ ε)) (ℤ*-comm (pos (2^ n₁)) k') ⟩
       k' ℤ* pos (2^ n₁) ℤ* pos (2^ ε)
         ＝⟨ ap (λ z → k' ℤ* pos (2^ n₁) ℤ* pos (2^ z)) e₂ ⟩
       k' ℤ* pos (2^ n₁) ℤ* pos (2^ (ε' +ℕ n₂))
         ＝⟨ ℤ*-assoc k' (pos (2^ n₁)) (pos (2^ (ε' +ℕ n₂))) ⟩
       k' ℤ* (pos (2^ n₁) ℤ* pos (2^ (ε' +ℕ n₂)))
         ＝⟨ ap (k' ℤ*_)
               (pos-multiplication-equiv-to-ℕ (2^ n₁) (2^ (ε' +ℕ n₂))) ⟩
       k' ℤ* pos ((2^ n₁) ℕ* 2^ (ε' +ℕ n₂))
         ＝⟨ ap (λ z →  k' ℤ* pos ((2^ n₁) ℕ* z)) (prod-of-powers 2 ε' n₂ ⁻¹) ⟩
       k' ℤ* pos (2^ n₁ ℕ* (2^ ε' ℕ* 2^ n₂))
         ＝⟨ ap (λ z → k' ℤ* pos z)
               (mult-associativity (2^ n₁) (2^ ε') (2^ n₂) ⁻¹) ⟩
       k' ℤ* pos (2^ n₁ ℕ* 2^ ε' ℕ* 2^ n₂)
         ＝⟨ ap (λ z → k' ℤ* pos (z ℕ* 2^ n₂))
               (mult-commutativity (2^ n₁) (2^ ε')) ⟩
       k' ℤ* pos (2^ ε' ℕ* 2^ n₁ ℕ* 2^ n₂)
         ＝⟨ ap (λ z → k' ℤ* pos z)
               (mult-associativity (2^ ε') (2^ n₁) (2^ n₂)) ⟩
       k' ℤ* pos (2^ ε' ℕ* (2^ n₁ ℕ* 2^ n₂))
         ＝⟨ ap (λ z → k' ℤ* z)
               (pos-multiplication-equiv-to-ℕ (2^ ε') (2^ n₁ ℕ* 2^ n₂) ⁻¹) ⟩
       k' ℤ* (pos (2^ ε') ℤ* pos (2^ n₁ ℕ* 2^ n₂))
         ＝⟨ ap (λ z → k' ℤ* (pos (2^ ε') ℤ* pos z)) (prod-of-powers 2 n₁ n₂) ⟩
       k' ℤ* (pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂)))
         ＝⟨ ℤ*-assoc k' (pos (2^ ε')) (pos (2^ (n₁ +ℕ n₂))) ⁻¹ ⟩
       k' ℤ* pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂))    ∎ -}
 {-
 normalise-≤'' : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
             → k ℤ* pos (2^ (succ δ)) ≤ m ℤ* pos (2^ (succ ε))
             → normalise (k , negsucc δ) ≤ normalise (m , negsucc ε)
 normalise-≤'' (k , δ) (m , ε)
  with (from-×-＝' (normalise-neg' k δ) , from-×-＝' (normalise-neg' m ε))
 ... | ((e₁ , e₂) , e₃ , e₄)
  = transport₂ _≤_
    (ℤ*-comm k (pos (2^ (succ δ)))
    ∙ ap₂ (λ z z' → z ℤ* pos (2^ z')) (e₁ ⁻¹) (e₄ ⁻¹))
    (ℤ*-comm m (pos (2^ (succ ε)))
    ∙ ap₂ (λ z z' → z ℤ* pos (2^ z')) (e₃ ⁻¹) (e₂ ⁻¹)) -}
```

