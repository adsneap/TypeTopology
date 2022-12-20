```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --without-K
            --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order hiding (≤-refl)
open import UF.Base
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Todd.BelowAndAbove
  using (downLeft-upRight ; downRight-upRight ; dL-transform)
open import Todd.DyadicRationals
  renaming (1/2ℤ[1/2] to 1/2; normalise to quotient)
open import Todd.Prelude 
open import Todd.upValue

module Todd.FunctionEncodings
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
  (dy : Dyadics)
 where

open import Todd.DyadicReals pe pt fe dy renaming (located to located')
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι)

open PropositionalTruncation pt
open Dyadics dy
  renaming ( _ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_
           ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order
  renaming (max to ℕmax) hiding (≤-refl ; ≤-trans ; ≤-split)
```

# Part I - Real numbers from sequences of dyadic-rational intervals

We use the type ℤ[1/2] × ℤ[1/2] to encode intervals of dyadic rational numbers.

`ld` and `rd` are used to get the lower and upper endpoints, respectively.

```
ld rd : ℤ[1/2] × ℤ[1/2] → ℤ[1/2]
ld (l , r) = l
rd (l , r) = r
```

An interval [la,ra] covers another interval [lb,rb] if la ≤ lb and rb ≤ ra.

```
_covers_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇
a covers b = (ld a ≤ ld b) × (rd b ≤ rd a)

covers-refl : (ab : ℤ[1/2] × ℤ[1/2]) → ab covers ab
covers-refl (a , b) = ≤-refl a , ≤-refl b

covers-trans : (a b c : ℤ[1/2] × ℤ[1/2]) → a covers b → b covers c → a covers c
covers-trans a b c (l≤₁ , r≤₁) (l≤₂ , r≤₂)
 = trans' (ld a) (ld b) (ld c) l≤₁ l≤₂
 , trans' (rd c ) (rd b) (rd a) r≤₂ r≤₁
```

We define three key properties for sequences of dyadic intervals
ζ : ℤ → ℤ[1/2] × ℤ[1/2]. 

```
intervalled nested located : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
intervalled ζ = (n : ℤ) → pr₁ (ζ n) ≤ pr₂ (ζ n)
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
located     ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
              → Σ n ꞉ ℤ , (pr₂ (ζ n) - pr₁ (ζ n)) ≤ ϵ

fully-nested' : (ℤ → ℤ[1/2] × ℤ[1/2]) → ℕ → 𝓤₀ ̇
fully-nested' ζ k = (n : ℤ) → (ζ n) covers (ζ (n +pos k))

fully-nested : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
fully-nested ζ = (n m : ℤ) → n ≤ m → (ζ n) covers (ζ m)

nested-implies-fully-nested'
 : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → Π (fully-nested' ζ)
nested-implies-fully-nested' ζ ρ 0 n = (0 , refl) , (0 , refl)
nested-implies-fully-nested' ζ ρ (succ k) n
 = covers-trans (ζ n) (ζ (succℤ n)) (ζ (succℤ (n +pos k))) (ρ n)
     (nested-implies-fully-nested' (ζ ∘ succℤ) (ρ ∘ succℤ) k n)

nested-implies-fully-nested
 : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → fully-nested ζ
nested-implies-fully-nested ζ ρ n m (k , refl)
 = nested-implies-fully-nested' ζ ρ k n

fully-nested-implies-nested
 : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → fully-nested ζ → nested ζ
fully-nested-implies-nested ζ ρ n = ρ n (succℤ n) (1 , refl)
```

Any sequence of dyadic intervals that satisfies these three properties yields a
real number.

```
⦅_⦆ : (ζ : ℤ → ℤ[1/2] × ℤ[1/2])
      → intervalled ζ → nested ζ → located ζ
      → ℝ-d
⦅ ζ ⦆ ζinv ζnes ζloc = (L , R)
 , inhabited-l , inhabited-r
 , rounded-l   , rounded-r
 , is-disjoint , is-located
 where
  L R : 𝓟 ℤ[1/2]
  L p = (∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))) , ∃-is-prop
  R q = (∃ n ꞉ ℤ , (rd (ζ n) <ℤ[1/2] q)) , ∃-is-prop
  
  inhabited-l : inhabited-left L
  inhabited-l = ∣ ld (ζ (pos 0)) - 1ℤ[1/2]
              , ∣ (pos 0) , (ℤ[1/2]<-neg (ld (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2]) ∣ ∣
  
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (rd (ζ (pos 0)) + 1ℤ[1/2])
              , ∣ pos 0  , ℤ[1/2]<-+ (rd (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))
        → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n')))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))
        → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n')))
      I (n , p<ζn) = let (p' , p<p' , p'<ζn) = dense p (ld (ζ n)) p<ζn
                     in p' , (p<p' , ∣ n , p'<ζn ∣)
    rtl : ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))
      I (p' , p<p' , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n)) → Σ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))
        II (n  , p'<ζn) = n , (trans p p' (ld (ζ n)) p<p' p'<ζn)
      
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , rd (ζ n) < q → ∃ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , rd (ζ n) < q → Σ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
      I (n , ζn<q) = let (q' , ζn<q' , q'<q) = dense (rd (ζ n)) q ζn<q
                     in q' , (q'<q , ∣ n , ζn<q' ∣)
    rtl : ∃ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
      I (q' , q'<q , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (rd (ζ n) < q') → Σ n ꞉ ℤ , (rd (ζ n) <ℤ[1/2] q)
        II (n , ζ<q') = n , (trans (rd (ζ n)) q' q ζ<q' q'<q)
  
  is-disjoint : disjoint L R
  is-disjoint p q (tp<x , tx<q)
   = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))) × (Σ n' ꞉ ℤ , (rd (ζ n') <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n'
           = let p<l' = ℤ[1/2]<-≤ p (ld (ζ n)) (ld (ζ n')) p<l
                          (pr₁ (nested-implies-fully-nested ζ ζnes n n' n≤n'))
                 l<q' = ℤ[1/2]≤-< (ld (ζ n')) (rd (ζ n')) q (ζinv n') r<q 
           in trans p (ld (ζ n')) q p<l' l<q'
    ... | inr n'≤n
           = let p<r' = ℤ[1/2]<-≤ p (ld (ζ n)) (rd (ζ n)) p<l (ζinv n)
                 r<q' = ℤ[1/2]≤-< (rd (ζ n)) (rd (ζ n')) q
                          (pr₂ (nested-implies-fully-nested ζ ζnes n' n n'≤n))
                             r<q
           in trans p (rd (ζ n)) q p<r' r<q'
 
  is-located : located' L R
  is-located p q p<q
   = I (ζloc (1/2 * (q - p))
       (ℤ[1/2]<-positive-mult 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)))
   where
    0<ε : 0ℤ[1/2] < (1/2 * (q - p))
    0<ε = <-pos-mult' 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((rd (ζ n) - ld (ζ n)) ≤ℤ[1/2] (1/2 * (q - p))))
      → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (rd (ζ n)) (ld (ζ n)) q p l₂)
     where
      l₂ :(rd (ζ n) - ld (ζ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (rd (ζ n) - ld (ζ n)) (1/2 * (q - p)) (q - p) l₁
             (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : rd (ζ n) < q ∔ p < ld (ζ n) → (L p holds) ∨ (R q holds)
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣
```

# Part II - Variable and specific-width interval sequences

We now define the type of variable-width and specific-width interval encodings
using integers.

The idea is that a variable-width interval code `(l,r,i) : 𝕀v` (given by
endpoint codes `l,r : ℤ`, such that l ≤ r, and a precision-level `i : ℤ`)
encodes the interval `[l/2^i,r/2^i]`.

Meanwhile, a specific-width interval code `(k,i) : 𝕀s` encodes the interval
`[k/2^i,(k+2)/2^i]`.

```
𝕀v 𝕀s : 𝓤₀  ̇
𝕀v = Σ ((l , r) , i) ꞉ ((ℤ × ℤ) × ℤ) , l ≤ r 
𝕀s = ℤ × ℤ

l r : ℤ × ℤ → ℤ[1/2]
l (k , i) = quotient (k        , i)
r (k , i) = quotient (k +pos 2 , i)

vwi : 𝕀v → ℤ[1/2] × ℤ[1/2]
vwi (((k , c) , i) , _) = l (k , i) , l (c , i)

swi : 𝕀s → ℤ[1/2] × ℤ[1/2]
swi (k     , i) = l (k , i) , r (k , i)

v-left v-right v-prec : 𝕀v → ℤ
v-l≤r  : (z : 𝕀v) → v-left z ≤ v-right z
v-left   = pr₁ ∘ pr₁ ∘ pr₁
v-right  = pr₂ ∘ pr₁ ∘ pr₁
v-prec   = pr₂ ∘ pr₁
v-l≤r    = pr₂

v-dist : 𝕀v → ℕ
v-dist z = pr₁ (v-l≤r z)
```

Every specific-width interval code gives a variable-width interval code.
Furthermore, a sequence of either gives a sequence of dyadic-rational intervals.

```
sw-to-vw : 𝕀s → 𝕀v
sw-to-vw (k , i) = ((k , k +pos 2) , i) , (2 , refl)

seq-sw-to-vw : (ℤ → 𝕀s) → (ℤ → 𝕀v)
seq-sw-to-vw = sw-to-vw ∘_

seq-of-vw-intervals : (ℤ → 𝕀v) → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-vw-intervals = vwi ∘_

seq-of-sw-intervals : (ℤ → 𝕀s)  → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-sw-intervals = swi ∘_

seq-convert-＝ : seq-of-sw-intervals ＝ (seq-of-vw-intervals ∘ seq-sw-to-vw)
seq-convert-＝ = refl
```

TODO: Move to Prelude.lagda.md

```
_preserves_as_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (X → 𝓦 ̇ ) → (Y → 𝓣 ̇ )
               → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ 
f preserves A as B  = ∀ x → A x → B (f x)

_preserves_ : {X : 𝓤 ̇ } → (X → X) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓦 ̇
f preserves A = f preserves A as A

preserves-trans : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓤' ̇ }
                → (f : X → Y) → (g : Y → Z)
                → (A : X → 𝓦 ̇ ) → (B : Y → 𝓣 ̇ ) → (C : Z → 𝓥' ̇ )
                → f preserves A as B
                → g preserves B as C
                → (g ∘ f) preserves A as C
preserves-trans f g A B C p₁ p₂ x Ax = p₂ (f x) (p₁ x Ax)
```

Now we define the three key properties on sequences of dyadic intervals on
variable-width encodings.

We show that the properties are equivalent to each other where necessary.

```
vw-intervalled vw-nested vw-located : (ℤ → 𝕀v) → 𝓤₀ ̇
vw-intervalled ζ = (n : ℤ) → v-left (ζ n) ≤ v-right (ζ n)
vw-nested        = nested ∘ seq-of-vw-intervals
vw-located     ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
                 → Σ n ꞉ ℤ , l (pos (v-dist (ζ n)) , v-prec (ζ n)) ≤ ϵ

vw-fully-nested : (ℤ → 𝕀v) → 𝓤₀ ̇
vw-fully-nested = fully-nested ∘ seq-of-vw-intervals

vw-is-intervalled : Π vw-intervalled
vw-is-intervalled = v-l≤r ∘_

vw-intervalled-preserves
  : seq-of-vw-intervals preserves vw-intervalled as intervalled
vw-intervalled-preserves ζ vwi n
  = normalise-≤2 (v-left (ζ n)) (v-right (ζ n)) (v-prec (ζ n)) (v-l≤r (ζ n))

v-dist-lemma
 : (ζ : ℤ → 𝕀v) → (n : ℤ) → l (pos (v-dist (ζ n)) , v-prec (ζ n))
 ＝ (l (v-right (ζ n) , v-prec (ζ n)) - l (v-left (ζ n) , v-prec (ζ n)))

vw-located-preserves : seq-of-vw-intervals preserves vw-located as located
vw-located-preserves ζ vwl ε ϵ-is-positive with vwl ε ϵ-is-positive
... | (n , l) = n , (transport (_≤ ε) (v-dist-lemma ζ n) l)

v-dist-lemma ζ n = II
 where
  get-e : v-left (ζ n) ℤ+ pos (v-dist (ζ n)) ＝ v-right (ζ n)
  get-e = pr₂ (v-l≤r (ζ n))
  I : pos (v-dist (ζ n)) ＝ v-right (ζ n) ℤ- v-left (ζ n)
  I = pos (v-dist (ζ n))
        ＝⟨ ℤ-zero-right-neutral (pos (v-dist (ζ n))) ⁻¹ ⟩
      pos (v-dist (ζ n)) ℤ+ pos 0
        ＝⟨ ap (pos (v-dist (ζ n)) ℤ+_)
              (ℤ-sum-of-inverse-is-zero (v-left (ζ n)) ⁻¹) ⟩
      pos (v-dist (ζ n)) ℤ+ (v-left (ζ n) ℤ- v-left (ζ n))
        ＝⟨ ℤ+-assoc (pos (v-dist (ζ n))) (v-left (ζ n)) (ℤ- v-left (ζ n)) ⁻¹ ⟩
      pos (v-dist (ζ n)) ℤ+ v-left (ζ n) ℤ- v-left (ζ n)
        ＝⟨ ap (_ℤ- v-left (ζ n))
              (ℤ+-comm (pos (v-dist (ζ n))) (v-left (ζ n))) ⟩
      v-left (ζ n) ℤ+ pos (v-dist (ζ n)) ℤ- v-left (ζ n)
        ＝⟨ ap (_ℤ- v-left (ζ n)) (pr₂ (v-l≤r (ζ n))) ⟩
      v-right (ζ n) ℤ- v-left (ζ n) ∎
  II : l (pos (v-dist (ζ n)) , v-prec (ζ n))
     ＝ l (v-right (ζ n) , v-prec (ζ n)) - l (v-left (ζ n) , v-prec (ζ n))
  II = l (pos (v-dist (ζ n)) , v-prec (ζ n))
         ＝⟨ ap (λ z →  l (z , v-prec (ζ n))) I ⟩
       l (v-right (ζ n) ℤ- v-left (ζ n) , (v-prec (ζ n)))
         ＝⟨ normalise-negation
               (v-right (ζ n)) (v-left (ζ n)) (v-prec (ζ n)) ⁻¹ ⟩
       l (v-right (ζ n) , v-prec (ζ n)) - l (v-left (ζ n) , v-prec (ζ n)) ∎
```

Then, we do the same for specific-width encodings.

```
sw-intervalled sw-nested sw-located : (ℤ → 𝕀s) → 𝓤₀ ̇ 
sw-intervalled = vw-intervalled ∘ seq-sw-to-vw
sw-nested      = vw-nested      ∘ seq-sw-to-vw
sw-located ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
             → Σ n ꞉ ℤ , l (pos 2 , pr₂ (ζ n)) ≤ ϵ

sw-fully-nested : (ℤ → 𝕀s) → 𝓤₀ ̇
sw-fully-nested = vw-fully-nested ∘ seq-sw-to-vw

sw-is-intervalled : Π sw-intervalled
sw-is-intervalled ζ n = 2 , refl

sw-located-preserves-vw : seq-sw-to-vw preserves sw-located as vw-located
sw-located-preserves-vw ζ = id

sw-located-preserves : seq-of-sw-intervals preserves sw-located as located
sw-located-preserves
 = preserves-trans seq-sw-to-vw _ _ _ located sw-located-preserves-vw vw-located-preserves

covers-is-prop : ∀ a b → is-prop (a covers b)
covers-is-prop a b = ×-is-prop (≤ℤ[1/2]-is-prop (ld a) (ld b)) (≤ℤ[1/2]-is-prop (rd b) (rd a))

sw-nested-is-prop : ∀ ζ → is-prop (sw-nested ζ)
sw-nested-is-prop ζ = Π-is-prop (fe 𝓤₀ 𝓤₀) λ _ → covers-is-prop _ _
```

# Part III - Normalised and prenormalised specific-width sequences

We now define what it means for a specific-width sequence encoding to be
normalised and prenormalised.

```
is-normalised    : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
is-normalised    ζ = (n : ℤ) → pr₂ (ζ n) ＝ n

is-prenormalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-prenormalised ζ = (n : ℤ) → pr₂ (ζ n) ≥ n

normalised-implies-prenormalised : (ζ : ℤ → 𝕀s)
                                 → is-normalised ζ
                                 → is-prenormalised ζ 
normalised-implies-prenormalised ζ ρ n = 0 , (ρ n ⁻¹)
```

The `upRight` function can be extended to specific-width intervals.
We define this, and prove a variety of properties related to it.

```
upRight* : 𝕀s → 𝕀s
upRight* (c , i) = upRight c , predℤ i

upRight-𝕀s : ℕ → 𝕀s → 𝕀s
upRight-𝕀s 0 = id
upRight-𝕀s (succ k) = upRight-𝕀s k ∘ upRight*

-- TODO: Move or find elsewhere
pred-shift : ∀ a b → predℤ a ℤ- b ＝ a ℤ- succℤ b
pred-shift a b = ℤ-left-pred a (ℤ- b)
               ∙ ℤ-right-pred a (ℤ- b) ⁻¹
               ∙ ap (a ℤ+_) (succℤ-lc (succpredℤ _ ∙ succpredℤ _ ⁻¹
                                      ∙ ap succℤ (negation-dist b (pos 1))))

upRight-𝕀s-＝ : ∀ k c i → pr₂ (upRight-𝕀s k (c , i)) ＝ i ℤ- pos k
upRight-𝕀s-＝ zero c i = refl
upRight-𝕀s-＝ (succ k) c i = upRight-𝕀s-＝ k (upRight c) (predℤ i)
                          ∙ pred-shift i (pos k)
                          
upRight-covers : (ci : 𝕀s) → swi (upRight* ci) covers swi ci
upRight-covers (c , i) = leftproof c i , rightproof c i
 where
   leftproof : ∀ c n → quotient (upRight c , predℤ n) ≤ quotient (c , n) 
   leftproof c n = transport (_≤ quotient (c , n)) II I
    where
      I : quotient (pos 2 ℤ* upRight c , n) ≤ quotient (c , n)
      I = normalise-≤2 (pos 2 ℤ* upRight c) c n (transport (_≤ c)
            (ℤ*-comm (upRight c) (pos 2)) (downLeft-upRight c))

      II : quotient (pos 2 ℤ* upRight c , n) ＝ quotient (upRight c , predℤ n)
      II = normalise-pred' (upRight c) n ⁻¹

   rightproof : (c n : ℤ)
              → quotient (c ℤ+ pos 2 , n)
              ≤ quotient (upRight c ℤ+ pos 2 , predℤ n)
   rightproof c n = transport (quotient (c ℤ+ pos 2 , n) ≤_) II I
    where
      II : quotient (pos 2 ℤ* (upRight c ℤ+ pos 2) , n)
         ＝ quotient (upRight c ℤ+ pos 2 , predℤ n)
      II = normalise-pred' (upRight c ℤ+ pos 2) n ⁻¹

      IV : c ℤ+ pos 2 ≤ (upRight c ℤ* pos 2 ℤ+ pos 2) ℤ+ pos 2
      IV = ℤ≤-adding' c (upRight c ℤ* pos 2 ℤ+ pos 2) (pos 2)
             (downRight-upRight c)

      V : upRight c ℤ* pos 2 ℤ+ pos 2 ℤ+ pos 2 ＝ pos 2 ℤ* (upRight c ℤ+ pos 2)
      V = upRight c ℤ* pos 2 ℤ+ pos 2 ℤ+ pos 2
            ＝⟨ ℤ+-assoc (upRight c ℤ* pos 2) (pos 2) (pos 2) ⟩
          upRight c ℤ* pos 2 ℤ+ (pos 2 ℤ* pos 2)
            ＝⟨ distributivity-mult-over-ℤ (upRight c) (pos 2) (pos 2) ⁻¹ ⟩
          (upRight c ℤ+ pos 2) ℤ* pos 2
            ＝⟨ ℤ*-comm (upRight c ℤ+ pos 2) (pos 2) ⟩
          pos 2 ℤ* (upRight c ℤ+ pos 2) ∎

      III : c ℤ+ pos 2 ≤ pos 2 ℤ* (upRight c ℤ+ pos 2)
      III = transport (c ℤ+ pos 2 ≤_) V IV
 
      I : quotient (c ℤ+ pos 2 , n)
        ≤ quotient (pos 2 ℤ* (upRight c ℤ+ pos 2) , n)
      I = normalise-≤2 (c ℤ+ pos 2) (pos 2 ℤ* (upRight c ℤ+ pos 2)) n III

upRight-preserves-order : (x y : 𝕀s) → quotient x ≤ quotient y
                        → quotient (upRight* x) ≤ quotient (upRight* y)
upRight-preserves-order x y = {!!}

upRight-preserves-covering : (ci kj : 𝕀s) → swi ci covers swi kj
                           → swi (upRight* ci) covers swi (upRight* kj)
upRight-preserves-covering (c , i) (k , j) ((n , v₁) , v₂) = to1 , to2
 where
  from1 : quotient (c , i) ≤ quotient (k , j)
  from1 = n , v₁

  from2 : quotient (k ℤ+ pos 2 , j) ≤ quotient (c ℤ+ pos 2 , i)
  from2 = v₂

  to1 to1' : quotient (upRight c , predℤ i) ≤ quotient (upRight k , predℤ j)
  to1 = upRight-preserves-order (c , i) (k , j) (n , v₁)
  to1' = {!n / 2 !} , {!!}

  to2 : quotient ((upRight k +pos 2) , predℤ j)
      ≤ quotient ((upRight c +pos 2) , predℤ i)
  to2 = {!!}

upRight-covers-lemma : ((c , i) (k , j) : 𝕀s) → i < j
                     → swi (c , i) covers swi (k , j)
                     → swi (c , i) covers swi (upRight* (k , j))
upRight-covers-lemma (c , i) (k , j) i<j v = {!!} , {!!}

upRight-covers' : (ci kj : 𝕀s) → swi ci covers swi kj
                → swi (upRight* ci) covers swi kj
upRight-covers' _ _ = covers-trans _ _ _ (upRight-covers _)

upRightⁿ-covers : (k : ℕ) → (ci : 𝕀s) → swi (upRight-𝕀s k ci) covers swi ci
upRightⁿ-covers 0 _ = covers-refl _
upRightⁿ-covers (succ k) ci
 = covers-trans _ _ _ (upRightⁿ-covers k (upRight* ci)) (upRight-covers ci)

upRightⁿ-covers' : (k : ℕ) → (ci kj : 𝕀s) → swi ci covers swi kj
                 → swi (upRight-𝕀s k ci) covers swi kj
upRightⁿ-covers' _ _ _ = covers-trans _ _ _ (upRightⁿ-covers _ _)

upRight-≤'-covers
 : (k₁ k₂ : ℕ) → ((c , i) (k , j) : 𝕀s) → i ℤ- pos k₁ ≤ j ℤ- pos k₂
 → swi (c , i) covers swi (k , j)
 → swi (upRight-𝕀s k₁ (c , i)) covers swi (upRight-𝕀s k₂ (k , j))
upRight-≤'-covers k₁ zero (c , i) (k , j) k≤
 = upRightⁿ-covers' k₁ (c , i) (k , j)
upRight-≤'-covers zero (succ k₂) (c , i) (k , j) k≤ v
 = upRight-≤'-covers 0 k₂ (c , i) (upRight* (k , j))
     (ℤ≤-trans _ _ _ k≤ (1 , (ap succℤ {!!} ∙ succpredℤ _)))
     (upRight-covers-lemma (c , i) (k , j) {!!} v)
upRight-≤'-covers (succ k₁) (succ k₂) (c , i) (k , j) k≤ v
 = upRight-≤'-covers k₁ k₂ (upRight* (c , i)) (upRight* (k , j))
     (transport₂ _≤_
        (pred-shift i (pos k₁) ⁻¹)
        (pred-shift j (pos k₂) ⁻¹) k≤)
     (upRight-preserves-covering (c , i) (k , j) v)
```

Next, we use `upRight-𝕀s` to define `go-up`, a functional that takes a schema
function k : ℤ → ℕ and a specific-width sequence encoding ζ, and returns a
specific-width sequence encoding that takes each (ζ n) upRight (k n)-many times.

```
go-up : (ℤ → ℕ) → (ζ : ℤ → 𝕀s) → (ℤ → 𝕀s)
go-up k ζ n = upRight-𝕀s (k n) (ζ n)
```

We use this to define `normalise`, which brings a prenormalised funciton
`upRight` the appropriate amount to normalise it.

```
normalise : (ζ : ℤ → 𝕀s) → is-prenormalised ζ → (ℤ → 𝕀s)
normalise ζ ρ = go-up (λ n → pr₁ (ρ n)) ζ

normalise-yields-normalised : (ζ : ℤ → 𝕀s) → (ρ : is-prenormalised ζ)
                            → is-normalised (normalise ζ ρ)
normalise-yields-normalised ζ ρ n 
  = upRight-𝕀s-＝ (pr₁ (ρ n)) (pr₁ (ζ n)) (pr₂ (ζ n))
  ∙ ap (_ℤ- pos k) (pr₂ (ρ n) ⁻¹)
  ∙ ℤ+-assoc _ _ _
  ∙ ap (n ℤ+_) (ℤ-sum-of-inverse-is-zero₀ k)
 where k = pr₁ (ρ n)
```

Normalisation preserves locatedness and nestedness.

```
normalised-is-located : (ζ : ℤ → 𝕀s) → (ρ : is-normalised ζ) → sw-located ζ
normalised-is-located ζ ρ ϵ ϵ-is-positive with ℤ[1/2]-find-lower ϵ ϵ-is-positive
... | (k , l) = k , (<-is-≤ℤ[1/2] (quotient (pos 2 , pr₂ (ζ k))) ϵ (transport (λ - → quotient (pos 2 , -) <ℤ[1/2] ϵ) (ρ k ⁻¹) l))

go-up-preserves-fully-nested
 : (k : ℤ → ℕ) (ζ : ℤ → 𝕀s)
 → ((n m : ℤ) → n ≤ m → (pr₂ (ζ n) ℤ- pos (k n)) ≤ (pr₂ (ζ m) ℤ- pos (k m)))
 → sw-fully-nested ζ
 → sw-fully-nested (go-up k ζ)
go-up-preserves-fully-nested k ζ f ρ n m n≤m
 = upRight-≤'-covers (k n) (k m) (ζ n) (ζ m) (f n m n≤m) (ρ n m n≤m)

normalise-preserves-fully-nested : (ζ : ℤ → 𝕀s) → (ρ : is-prenormalised ζ)
                                 → sw-fully-nested ζ
                                 → sw-fully-nested (normalise ζ ρ)
normalise-preserves-fully-nested ζ ρ
 = go-up-preserves-fully-nested (λ n → pr₁ (ρ n)) ζ γ
 where
   γ : _
   γ n m
    = transport₂ (λ ■₁ ■₂ → ■₁ ℤ- pos (pr₁ (ρ n)) ≤ ■₂ ℤ- pos (pr₁ (ρ m)))
        (pr₂ (ρ n)) (pr₂ (ρ m))
    ∘ (transport₂ _≤_ (e n (pos (pr₁ (ρ n))) ⁻¹) (e m (pos (pr₁ (ρ m))) ⁻¹))
    where
      e : ∀ a b → ((a ℤ+ b) ℤ- b) ＝ a -- TODO: Find this elsewhere
      e a b = ℤ+-assoc _ _ _ ∙ ap (a ℤ+_) (ℤ-sum-of-inverse-is-zero b)

normalise-preserves-nested : (ζ : ℤ → 𝕀s) → (ρ : is-prenormalised ζ)
                           → sw-nested ζ
                           → sw-nested (normalise ζ ρ)
normalise-preserves-nested ζ ρ swn
 = fully-nested-implies-nested _
     (normalise-preserves-fully-nested ζ ρ (nested-implies-fully-nested _ swn))
{-
go-up-covers : (ζ : ℤ → 𝕀s) → (μ : ℤ → ℕ) → (n : ℤ)
             →        seq-of-sw-intervals (go-up μ ζ) n
               covers seq-of-sw-intervals          ζ  n 
go-up-covers ζ μ n = {!refl!}
-}

```

# Part IV - Ternary Boehm Real encodings

Bringing in ternary Boehm real encodings from `TernaryBoehmReals.lagda.md`, we
first relate them to specific-width interval encodings.

```
TBR-to-sw-seq : 𝕋 → (ℤ → 𝕀s)
TBR-to-sw-seq (χ , b) n = χ n , n

TBR-to-sw-is-normalised : (χ : 𝕋) → is-normalised (TBR-to-sw-seq χ)
TBR-to-sw-is-normalised χ n = refl

normalised-nested-seq-yields-belowness : (χ : ℤ → 𝕀s) → is-normalised χ
                                       → sw-nested χ
                                       → (n : ℤ)
                                       → pr₁ (χ (succℤ n)) below pr₁ (χ n)
normalised-nested-seq-yields-belowness χ η nsted n = 2a≤b , b≤2a+2
 where
  a = pr₁ (χ n)
  b = pr₁ (χ (succℤ n))
 
  l₁ : quotient (a , pr₂ (χ n)) ≤ quotient (b , pr₂ (χ (succℤ n)))
  l₁ = pr₁ (nsted n)

  l₃ : quotient (a , n) ≤ quotient (b , succℤ n)
  l₃ = transport₂
         (λ ∎₁ ∎₂ → quotient (a , ∎₁) ≤ quotient (b , ∎₂))
         (η n) (η (succℤ n)) l₁

  l₅ : quotient (a ℤ* pos 2 , succℤ n) ≤ quotient (b , succℤ n)
  l₅ = transport (_≤  quotient (b , succℤ n)) (normalise-succ' a n) l₃

  2a≤b : a ℤ* pos 2 ≤ b
  2a≤b = from-normalise-≤-same-denom _ _ _ l₅

  l₂ : quotient (b +pos 2 , pr₂ (χ (succℤ n))) ≤ quotient (a +pos 2 , pr₂ (χ n))
  l₂ = pr₂ (nsted n)

  l₄ : quotient (b +pos 2 , succℤ n) ≤ quotient (a +pos 2 , n)
  l₄ = transport₂
         (λ ∎₁ ∎₂ → quotient (b +pos 2 , ∎₁ ) ≤ quotient (a +pos 2 , ∎₂))
         (η (succℤ n)) (η n) l₂

  l₆ : quotient (b +pos 2 , succℤ n) ≤ quotient (downLeft (a +pos 2) , succℤ n)
  l₆ = transport
         (quotient (b +pos 2 , succℤ n) ≤_) (normalise-succ' (a +pos 2) n) l₄

  l₇ : (b +pos 2) ≤ downLeft (a +pos 2)
  l₇ = from-normalise-≤-same-denom _ _ _ l₆

  I : downLeft (a +pos 2) ＝ succℤ (succℤ (downRight a))
  I = downLeft (a +pos 2)               ＝⟨ dL-transform (a +pos 1) ⟩
      (succℤ ^ 2) (downLeft (a +pos 1)) ＝⟨ ap (succℤ ^ 2) (dL-transform a) ⟩
      succℤ (succℤ (downRight a))       ∎
 
  b≤2a+2 : b ≤ downRight a
  b≤2a+2 = ≤-succℤ' b (downRight a)
           (≤-succℤ' (succℤ b) (succℤ (downRight a))
            (transport ((b +pos 2) ≤_) I l₇))

belowness-yields-nested-seq : (χ : ℤ → 𝕀s)
                            → ((n : ℤ) → pr₁ (χ (succℤ n)) below pr₁ (χ n))
                            → sw-nested χ
belowness-yields-nested-seq χ b n = γ₁ , {!γ₂!}
 where
  is-n : is-normalised (TBR-to-sw-seq ((λ n → pr₁ (χ n)) , b))
  is-n = TBR-to-sw-is-normalised (pr₁ ∘ χ , b)
  
  I : (downLeft (pr₁ (χ n)) ≤ pr₁ (χ (succℤ n)))
    × (pr₁ (χ (succℤ n)) ≤ downRight (pr₁ (χ n)))
  I = b n

  III : quotient (pr₁ (χ n) ℤ+ pr₁ (χ n) , succℤ (pr₂ (χ n)))
      ≤ quotient (pr₁ (χ (succℤ n))      , pr₂ (χ (succℤ n)))
  III = {!normalise-≤!}

  II : quotient (pr₁ (χ n) ℤ+ pr₁ (χ n) , succℤ (pr₂ (χ n)))
     ≤ quotient (pr₁ (χ (succℤ n))      , pr₂ (χ (succℤ n)))
  II = transport
         (λ ∎ → quotient (pr₁ (χ n) ℤ+ pr₁ (χ n) , ∎)
              ≤ quotient (pr₁ (χ (succℤ n))      , pr₂ (χ (succℤ n))))
         (is-n (succℤ (pr₂ (χ n)))) III

  γ₁ : quotient (χ n) ≤ quotient (χ (succℤ n))
  γ₁ = transport (_≤ quotient (χ (succℤ n)))
         (normalise-succ' (pr₁ (χ n)) (pr₂ (χ n)) ⁻¹) II

normalised-seq-to-TBR : (χ : ℤ → 𝕀s) → is-normalised χ → sw-nested χ → 𝕋
normalised-seq-to-TBR χ η₁ η₂
 = (pr₁ ∘ χ) , normalised-nested-seq-yields-belowness χ η₁ η₂

prenormalised-seq-to-TBR : (χ : ℤ → ℤ × ℤ) → is-prenormalised χ
                         → sw-nested χ → 𝕋
prenormalised-seq-to-TBR χ η₁ η₂ = normalised-seq-to-TBR (normalise χ η₁)
                                     (normalise-yields-normalised χ η₁)
                                     (normalise-preserves-nested χ η₁ η₂)
```

We use all of our infrastructure thus far to define the map from TBRs to ℝ.

```
⟦_⟧ : 𝕋 → ℝ-d
⟦ χ  ⟧ = ⦅ seq-of-vw-intervals (seq-sw-to-vw (TBR-to-sw-seq χ)) ⦆
            (vw-intervalled-preserves (seq-sw-to-vw (TBR-to-sw-seq χ))
               (sw-is-intervalled (TBR-to-sw-seq χ)))
            (belowness-yields-nested-seq (TBR-to-sw-seq χ) (pr₂ χ))
            (sw-located-preserves (TBR-to-sw-seq χ)
              (normalised-is-located (TBR-to-sw-seq χ)
                (TBR-to-sw-is-normalised χ)))
```

# Part V - Encoding functions from ℝ on 𝕋

We define the function `join'`, which converts a specific-width interval to the
narrowest variable width-interval possible.

This can be extended to sequences, which we call `join`.

```
join' : 𝕀v → 𝕀s
join' z = upRight-𝕀s (upValue (v-left z) (v-right z) (v-l≤r z))
                     (v-left z , v-prec z)

join : (ℤ → 𝕀v) → (ℤ → 𝕀s)
join = join' ∘_
```

We need to prove that `join` preserves nestedness, which requires the
completion of the following proofs.

```
upValue-covers-lemma : (a b c d : ℤ)
                     → (l₁ : a ≤ b) → (l₂ : b ≤ c) → (l₃ : c ≤ d) → (l₄ : a ≤ d)
                     → upValue b c l₂ ≤ upValue a d l₄
upValue-covers-lemma = {!!}

andrew-hole' : (ζn ζm : 𝕀v)
             → vwi ζn covers vwi ζm
             → v-prec ζn ≤ v-prec ζm
             → let up-n = upValue (v-left ζn) (v-right ζn) (v-l≤r ζn)
                   up-m = upValue (v-left ζm) (v-right ζm) (v-l≤r ζm) in
               v-prec ζn ℤ- (pos up-n) ≤ v-prec ζm ℤ- (pos up-m)
andrew-hole' (((ln , rn) , pn) , l≤rn) (((lm , rm) , pm) , l≤rm) v pn≤pm = γ
 where
  I : upValue lm rm l≤rm ≤ upValue ln rn l≤rn
  I = upValue-covers-lemma ln lm rm rn {!!} l≤rm {!!} l≤rn

  II : pos (upValue lm rm l≤rm) ≤ pos (upValue ln rn l≤rn)
  II = ℕ≤-to-ℤ≤ (upValue lm rm l≤rm) (upValue ln rn l≤rn) I

  III : ℤ- pos (upValue ln rn l≤rn) ≤ ℤ- pos (upValue lm rm l≤rm)
  III = ℤ≤-swap (pos (upValue lm rm l≤rm)) (pos (upValue ln rn l≤rn)) II

  γ : pn ℤ- pos (upValue ln rn l≤rn) ≤ pm ℤ- pos (upValue lm rm l≤rm)
  γ = ℤ≤-adding pn pm
        (ℤ- pos (upValue ln rn l≤rn))
        (ℤ- pos (upValue lm rm l≤rm))
        pn≤pm III

andrew-hole'' : (ζn ζm : 𝕀v)
              → vwi ζn covers vwi ζm
              → v-prec ζm ≤ v-prec ζn
              → let up-n = upValue (v-left ζn) (v-right ζn) (v-l≤r ζn)
                    up-m = upValue (v-left ζm) (v-right ζm) (v-l≤r ζm) in
                v-prec ζn ℤ- (pos up-n) ≤ v-prec ζm ℤ- (pos up-m)
andrew-hole'' (((ln , rn) , pn) , (α , α'))
              (((lm , rm) , pm) , (β , β')) v (z , e)
 = transport₂ _≤_ X XI IX
 where
  I : pos z ＝ pn ℤ- pm
  I = pos z                  ＝⟨ ap (_ ℤ+_) (ℤ-sum-of-inverse-is-zero _ ⁻¹) ⟩
      pos z ℤ+ (pm ℤ- pm)    ＝⟨ ℤ+-assoc _ _ _ ⁻¹ ⟩
      pos z ℤ+ pm ℤ+ (ℤ- pm) ＝⟨ ap (_ℤ- pm) (ℤ+-comm _ _) ⟩
      pm ℤ+ pos z ℤ- pm      ＝⟨ ap (_ℤ- pm) e  ⟩
      pn ℤ- pm               ∎
  II : pos (z ℕ+ upValue lm rm (β , β'))
     ＝ pn ℤ- (pm ℤ- pos (upValue lm rm (β , β'))) 
  II = pos (z ℕ+ upValue lm rm (β , β'))
         ＝⟨ distributivity-pos-addition z (upValue lm rm (β , β')) ⁻¹ ⟩
       pos z ℤ+ pos (upValue lm rm (β , β'))
         ＝⟨ ap (_ℤ+ pos (upValue lm rm (β , β'))) I ⟩
       pn ℤ- pm ℤ+ pos (upValue lm rm (β , β'))
         ＝⟨ ℤ+-assoc pn (ℤ- pm) (pos (upValue lm rm (β , β')))  ⟩
       pn ℤ+ ((ℤ- pm) ℤ+ pos (upValue lm rm (β , β')))
         ＝⟨ ap (λ ∎ → pn ℤ+ ((ℤ- pm) ℤ+ ∎))
                (minus-minus-is-plus (pos (upValue lm rm (β , β'))) ⁻¹) ⟩
       pn ℤ+ ((ℤ- pm) ℤ+ (ℤ- (ℤ- pos (upValue lm rm (β , β')))))
         ＝⟨ ap (pn ℤ+_) (negation-dist pm (ℤ- pos (upValue lm rm (β , β')))) ⟩
       pn ℤ- (pm ℤ- pos (upValue lm rm (β , β'))) ∎
  III : lm ℤ* pos (2^ z) ≤ rm ℤ* pos (2^ z)
  III = positive-multiplication-preserves-order' lm rm (pos (2^ z))
          (power-of-pos-positive z) (β , β')
  IV : z ℕ+ upValue lm rm (β , β')
     ≤ upValue (lm ℤ* pos (2^ z)) (rm ℤ* pos (2^ z)) III
  IV = {!!}
  
  V : upValue (lm ℤ* pos (2^ z)) (rm ℤ* pos (2^ z)) III
    ≤ upValue ln rn (α , α')
  V = {!!}
  
  VI : z ℕ+ upValue lm rm (β , β') ≤ upValue ln rn (α , α')
  VI = ≤-trans _ _ _ IV V
  
  VII : pos (z ℕ+ upValue lm rm (β , β')) ≤ pos (upValue ln rn (α , α'))
  VII = ℕ≤-to-ℤ≤ _ _ VI
  
  VIII : pn ℤ- (pm ℤ- pos (upValue lm rm (β , β')))
       ≤ pos (upValue ln rn (α , α'))
  VIII = transport (_≤ pos (upValue ln rn (α , α'))) II VII

  IX : {!!}
  IX = ℤ≤-adding' _ _
         (pm ℤ- pos (upValue lm rm (β , β')) ℤ- pos (upValue ln rn (α , α')))
         VIII  

  X : pn ℤ- (pm ℤ- pos (upValue lm rm (β , β')))
         ℤ+ (pm ℤ- pos (upValue lm rm (β , β'))
         ℤ- pos (upValue ln rn (α , α')))
    ＝ pn ℤ- pos (upValue ln rn (α , α'))
  X = ℤ+-assoc _ _ _ ⁻¹
    ∙ ap (_ℤ- _) (ℤ+-assoc _ _ _)
    ∙ ap (λ ∎ → _ ℤ+ ∎ ℤ- _) (ℤ-sum-of-inverse-is-zero' _)

  XI : pos (upValue ln rn (α , α'))
         ℤ+ (pm ℤ- pos (upValue lm rm (β , β'))
         ℤ- pos (upValue ln rn (α , α')))
     ＝ pm ℤ- pos (upValue lm rm (β , β'))
  XI = ap (_ ℤ+_) (ℤ+-comm _ _)
     ∙ ℤ+-assoc _ _ _ ⁻¹
     ∙ ap (_ℤ+ _) (ℤ-sum-of-inverse-is-zero _)
     ∙ ℤ-zero-left-neutral _ 

-- TODO: Rename
andrew-hole : (ζn ζm : 𝕀v) → vwi ζn covers vwi ζm
            → let up-n = upValue (v-left ζn) (v-right ζn) (v-l≤r ζn)
                  up-m = upValue (v-left ζm) (v-right ζm) (v-l≤r ζm) in
              v-prec ζn ℤ- (pos up-n) ≤ v-prec ζm ℤ- (pos up-m)
andrew-hole (((ln , rn) , pn) , l≤rn) (((lm , rm) , pm) , l≤rm) v
 with ℤ-trichotomous pn pm 
... | (inl pn<pm)
 = andrew-hole' (((ln , rn) , pn) , l≤rn) (((lm , rm) , pm) , l≤rm)
     v (<-is-≤ pn pm pn<pm)
... | inr (inl pn＝pm)
 = andrew-hole' (((ln , rn) , pn) , l≤rn) (((lm , rm) , pm) , l≤rm)
     v (transport (pn ≤_) pn＝pm (ℤ≤-refl pn))
... | inr (inr pm<pn)
 = andrew-hole'' (((ln , rn) , pn) , l≤rn) (((lm , rm) , pm) , l≤rm)
     v (<-is-≤ pm pn pm<pn)
```

Using these, we can show that join preserves nestedness.

```
join-preserves-fully-nested : (ζ : ℤ → 𝕀v) → vw-fully-nested ζ
                            → sw-fully-nested (join ζ)
join-preserves-fully-nested ζ v n m n≤m
 = upRight-≤'-covers (upValue (v-left (ζ n)) (v-right (ζ n)) (v-l≤r (ζ n)))
                     (upValue (v-left (ζ m)) (v-right (ζ m)) (v-l≤r (ζ m)))
                     (v-left (ζ n) , v-prec (ζ n))
                     (v-left (ζ m) , v-prec (ζ m))
                     (andrew-hole _ _ (v n m n≤m))
                     {!!} -- Todd

join-preserves-nested : (ζ : ℤ → 𝕀v) → vw-nested ζ → sw-nested (join ζ)
join-preserves-nested ζ v
 = fully-nested-implies-nested
     (seq-of-sw-intervals (join ζ))
     (join-preserves-fully-nested ζ
       (nested-implies-fully-nested
         (seq-of-vw-intervals ζ) v))
```

The following record defines our  machinery for converting functions on the real
space to encoded functions on ternary Boehm encodings. This uses approximators
and continuity oracles, as defined in the paper.

```
record FunctionMachine (d : ℕ) : 𝓤₁  ̇ where
  field
    f  : Vec ℝ-d d → ℝ-d
    A  : Vec 𝕀v d → 𝕀v
    κ : Vec 𝕋 d → ℤ → Vec ℤ d
    κ-is-coracle
      : (χs : Vec 𝕋 d) → (ϵ : ℤ)
      → pr₂
          (join'
            (A (vec-map₂ (vec-map (seq-sw-to-vw ∘ TBR-to-sw-seq) χs) (κ χs ϵ))))
        ≥ ϵ
  f̂'  : Vec (ℤ → 𝕀v) d → (k : ℤ → Vec ℤ d) → (ℤ → 𝕀v)
  f̂'  χs k n = A (vec-map₂ χs (k n))
  g'  : Vec (ℤ → 𝕀v) d → (k : ℤ → Vec ℤ d) → (ℤ → 𝕀v)
  g'  χs k n = A (vec-map₂ χs (k n))
  f̂'' : Vec (ℤ → 𝕀s) d → (k : ℤ → Vec ℤ d) → (ℤ → 𝕀s)
  f̂'' χs k = join (f̂' (vec-map seq-sw-to-vw χs) k)
  κ'-is-coracle : (χs : Vec 𝕋 d)
                → is-prenormalised (f̂'' (vec-map TBR-to-sw-seq χs) (κ χs))
  κ'-is-coracle χs ϵ
   = transport (λ ■ → ϵ ≤ pr₂ (join' (A (vec-map₂ ■ (κ χs ϵ)))))
       (vec-map-∼ TBR-to-sw-seq seq-sw-to-vw χs)
       (κ-is-coracle χs ϵ)
  f̂   : Vec 𝕋 d → 𝕋
  f̂   χs   = prenormalised-seq-to-TBR
                 (f̂'' (vec-map TBR-to-sw-seq χs) (κ χs))
               (κ'-is-coracle χs)
               (join-preserves-nested
                 (f̂' (vec-map (seq-sw-to-vw) (vec-map TBR-to-sw-seq χs)) (κ χs))
                 {!!})
```

# Part VI - Examples of function encodings

We have begun formalising examples of encoding functions by instantiating the
above record.

```
Negation : FunctionMachine 1
FunctionMachine.f Negation [ x ] = ℝd- x
FunctionMachine.A Negation [ (((l , r) , i) , l≤r) ]
                           = ((ℤ- r , ℤ- l) , i)
                           , ℤ≤-swap l r l≤r
FunctionMachine.κ Negation _ ϵ = [ ϵ ]
FunctionMachine.κ-is-coracle Negation [ χ ] ϵ = 0 , refl

_-min_ : ℤ → ℤ → ℕ
x -min y with ℤ-dichotomous x y
... | inl x≤y = 0
... | inr (n , refl) = n

Addition : FunctionMachine 2
FunctionMachine.f Addition (x ∷ [ y ]) = x ℝd+ y
FunctionMachine.A Addition
  ((((l₁ , r₁) , i₁) , l≤₁r) ∷ [ (((l₂ , r₂) , i₂) , l≤₂r) ])
  = ((pos (2^ (i₂  -min i₁)) ℤ* l₁ ℤ+ pos (2^ (i₁ -min i₂)) ℤ* l₂
    , (pos (2^ (i₂  -min i₁)) ℤ* r₁ ℤ+ pos (2^ (i₁ -min i₂)) ℤ* r₂))
    , maxℤ i₁ i₂)
    , {!!}
FunctionMachine.κ Addition _ ϵ = (ϵ +pos 2) ∷ [ ϵ +pos 2 ]
FunctionMachine.κ-is-coracle Addition (χ ∷ [ γ ]) ϵ = {!!}

𝕋-_ : 𝕋 → 𝕋
𝕋- x = FunctionMachine.f̂ Negation [ x ]
```

We conclude our work for the purpose of searchability in
`TernaryBoehmRealsSearch.lagda.md`.
