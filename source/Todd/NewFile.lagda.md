
```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient
open import UF.Powerset hiding (𝕋)

module Todd.NewFile
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.RationalsDyadic fe renaming (1/2ℤ[1/2] to 1/2; normalise to quotient)
open import Todd.DyadicReals pe pt fe renaming (located to located')
open import Todd.TBRFunctions pt fe pe sq
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import Todd.TBRDyadicReals pt fe pe sq
open import Todd.upValue
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp
  renaming (_ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_ ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

_≡_ = Id

-- Dyadic interval properties and sequences

ld rd : ℤ[1/2] × ℤ[1/2] → ℤ[1/2]
ld (l , r) = l
rd (l , r) = r

_covers_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇
a covers b = (ld a ≤ ld b) × (rd b ≤ rd a)

covers-trans : (a b c : ℤ[1/2] × ℤ[1/2]) → a covers b → b covers c → a covers c
covers-trans a b c (l≤₁ , r≤₁) (l≤₂ , r≤₂) = {!!} , {!!}

intervalled nested located intersected : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
intervalled ζ = (n : ℤ) → pr₁ (ζ n) ≤ pr₂ (ζ n)
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
located     ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , (pr₂ (ζ n) - pr₁ (ζ n)) ≤ ϵ
intersected ζ = (n m : ℤ) → min (pr₂ (ζ n)) (pr₂ (ζ m)) ≤ max (pr₁ (ζ n)) (pr₁ (ζ m))

fully-nested' : (ℤ → ℤ[1/2] × ℤ[1/2]) → ℕ → 𝓤₀ ̇
fully-nested' ζ k = (n : ℤ) → (ζ n) covers (ζ (n +pos k))

fully-nested : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
fully-nested ζ = (n m : ℤ) → n ≤ m → (ζ n) covers (ζ m)

nested-implies-fully-nested' : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → Π (fully-nested' ζ)
nested-implies-fully-nested' ζ ρ 0 n = (0 , refl) , (0 , refl)
nested-implies-fully-nested' ζ ρ (succ k) n
 = covers-trans (ζ n) (ζ (succℤ n)) (ζ (succℤ (n +pos k))) (ρ n)
     (nested-implies-fully-nested' (ζ ∘ succℤ) (ρ ∘ succℤ) k n)

nested-implies-fully-nested : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → fully-nested ζ
nested-implies-fully-nested ζ ρ n m (k , refl) = nested-implies-fully-nested' ζ ρ k n

nested-gives-intersected : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → intersected ζ
nested-gives-intersected ζ η n m = {!!}

⦅_⦆ : (ζ : ℤ → ℤ[1/2] × ℤ[1/2])
      → intervalled ζ → intersected ζ → located ζ
      → ℝ-d
⦅ ζ ⦆ ζinv ζins ζloc = (L , R)
 , inhabited-l , inhabited-r
 , rounded-l   , rounded-r
 , is-disjoint , is-located
 where
  L R : 𝓟 ℤ[1/2]
  L p = (∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))) , ∃-is-prop
  R q = (∃ n ꞉ ℤ , (rd (ζ n) <ℤ[1/2] q)) , ∃-is-prop
  
  inhabited-l : inhabited-left L
  inhabited-l = ∣ ld (ζ (pos 0)) - 1ℤ[1/2] , ∣ (pos 0) , (ℤ[1/2]<-neg (ld (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2]) ∣ ∣
  
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (rd (ζ (pos 0)) + 1ℤ[1/2])
              , ∣ pos 0  , ℤ[1/2]<-+ (rd (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n)) → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n')))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n)) → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (ζ n')))
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
  is-disjoint p q (tp<x , tx<q) = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] ld (ζ n))) × (Σ n' ꞉ ℤ , (rd (ζ n') <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n' = let p<l' = ℤ[1/2]<-≤ p (ld (ζ n)) (ld (ζ n')) p<l
                                  (pr₁ (nested-implies-fully-nested ζ {!!} n n' n≤n'))
                         l<q' = ℤ[1/2]≤-< (ld (ζ n')) (rd (ζ n')) q (ζinv n') r<q 
                     in trans p (ld (ζ n')) q p<l' l<q'
    ... | inr n'≤n = let p<r' = ℤ[1/2]<-≤ p (ld (ζ n)) (rd (ζ n)) p<l (ζinv n)
                         r<q' = ℤ[1/2]≤-< (rd (ζ n)) (rd (ζ n')) q
                                  (pr₂ (nested-implies-fully-nested ζ {!!} n' n n'≤n)) r<q
                     in trans p (rd (ζ n)) q p<r' r<q'
 
  is-located : located' L R
  is-located p q p<q = I (ζloc (1/2 * (q - p)))
   where
    0<ε : 0ℤ[1/2] < (1/2 * (q - p))
    0<ε = <-pos-mult' 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((rd (ζ n) - ld (ζ n)) ≤ℤ[1/2] (1/2 * (q - p)))) → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (rd (ζ n)) (ld (ζ n)) q p l₂)
     where
      l₂ :(rd (ζ n) - ld (ζ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (rd (ζ n) - ld (ζ n)) (1/2 * (q - p)) (q - p) l₁ (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : rd (ζ n) < q ∔ p < ld (ζ n) → (L p holds) ∨ (R q holds)
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣

l r : ℤ × ℤ → ℤ[1/2]
l (k , i) = quotient (k        , i)
r (k , i) = quotient (k +pos 2 , i)

-- Variable and specific width sequences

𝕀v 𝕀s : 𝓤₀  ̇
𝕀v = Σ ((l , r) , i) ꞉ ((ℤ × ℤ) × ℤ) , l ≤ r 
𝕀s = ℤ × ℤ

variable-width-interval : 𝕀v → ℤ[1/2] × ℤ[1/2]
variable-width-interval (((k , c) , i) , _) = l (k , i) , l (c , i)

specific-width-interval : 𝕀s → ℤ[1/2] × ℤ[1/2]
specific-width-interval (k     , i) = l (k , i) , r (k , i)

sw-to-vw : 𝕀s → 𝕀v
sw-to-vw (k , i) = ((k , k +pos 2) , i) , (2 , refl)

seq-sw-to-vw : (ℤ → 𝕀s) → (ℤ → 𝕀v)
seq-sw-to-vw = sw-to-vw ∘_

seq-of-vw-intervals : (ℤ → 𝕀v) → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-vw-intervals = variable-width-interval ∘_

seq-of-sw-intervals : (ℤ → 𝕀s)  → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-sw-intervals = specific-width-interval ∘_

seq-convert-≡ : seq-of-sw-intervals ≡ (seq-of-vw-intervals ∘ seq-sw-to-vw)
seq-convert-≡ = refl

-- Preserve definitions

_preserves_as_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (X → 𝓦 ̇ ) → (Y → 𝓣 ̇ ) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ 
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

-- Variable width sequence properties

v-left v-right v-prec : 𝕀v → ℤ
v-left   = pr₁ ∘ pr₁ ∘ pr₁
v-right  = pr₂ ∘ pr₁ ∘ pr₁
v-prec   = pr₂ ∘ pr₁
v-l≤r  : (z : 𝕀v) → v-left z ≤ v-right z
v-l≤r    = pr₂
v-dist : 𝕀v → ℕ
v-dist z = pr₁ (v-l≤r z)

vw-intervalled vw-nested vw-located : (ℤ → 𝕀v) → 𝓤₀ ̇
vw-intervalled ζ = (n : ℤ) → v-left (ζ n) ≤ v-right (ζ n)
vw-nested        = nested ∘ seq-of-vw-intervals
vw-located     ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , l (pos (v-dist (ζ n)) , v-prec (ζ n)) ≤ ϵ

vw-is-intervalled : Π vw-intervalled
vw-is-intervalled = v-l≤r ∘_

vw-intervalled-preserves : seq-of-vw-intervals preserves vw-intervalled as intervalled
vw-intervalled-preserves = {!!}

vw-located-preserves : seq-of-vw-intervals preserves vw-located as located
vw-located-preserves = {!!}

-- Specific width sequence properties

sw-intervalled sw-nested sw-located : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
sw-intervalled = vw-intervalled ∘ seq-sw-to-vw
sw-nested      = vw-nested      ∘ seq-sw-to-vw
sw-located ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , l (pos 2 , pr₂ (ζ n)) ≤ ϵ

sw-is-intervalled : Π sw-intervalled
sw-is-intervalled ζ n = 2 , refl

sw-located-preserves-vw : seq-sw-to-vw preserves sw-located as vw-located
sw-located-preserves-vw ζ ρ ϵ = {!!} , {!!}

sw-located-preserves : seq-of-sw-intervals preserves sw-located as located
sw-located-preserves
 = preserves-trans seq-sw-to-vw _ _ _ located sw-located-preserves-vw vw-located-preserves

-- Prenormalised and normalised

is-normalised    : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
is-normalised    ζ = (n : ℤ) → pr₂ (ζ n) ≡ n

is-prenormalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-prenormalised ζ = (n : ℤ) → pr₂ (ζ n) ≥ n

normalised-implies-prenormalised : (ζ : ℤ → 𝕀s)
                                 → is-normalised ζ
                                 → is-prenormalised ζ 
normalised-implies-prenormalised ζ ρ n = 0 , (ρ n ⁻¹)

go-up' : ℕ → 𝕀s → 𝕀s
go-up' k (c , i) = (upRight ^ k) c , i ℤ- pos k

go-up : (ℤ → ℕ) → (ζ : ℤ → 𝕀s) → (ℤ → 𝕀s)
go-up ρ ζ n = go-up' (ρ n) (ζ n)

normalise : (ζ : ℤ → 𝕀s) → is-prenormalised ζ → (ℤ → 𝕀s)
normalise ζ ρ = go-up (λ n → pr₁ (ρ n)) ζ

normalise-yields-normalised : (ζ : ℤ → 𝕀s) → (ρ : is-prenormalised ζ)
                            → is-normalised (normalise ζ ρ)
normalise-yields-normalised ζ ρ n
  = ap (_ℤ- pos k) (pr₂ (ρ n) ⁻¹)
  ∙ ℤ+-assoc _ _ _
  ∙ ap (n ℤ+_) (ℤ-sum-of-inverse-is-zero₀ k)
 where k = pr₁ (ρ n)

-- Normalised sequence properties

normalised-is-located : (ζ : ℤ → 𝕀s) → (ρ : is-normalised ζ) → sw-located ζ
normalised-is-located ζ ρ ϵ = {!clog₂ ϵ!} , {!!}

normalise-preserves-nested : (ζ : ℤ → 𝕀s) → (ρ : is-prenormalised ζ)
                           → sw-nested ζ
                           → sw-nested (normalise ζ ρ)
normalise-preserves-nested = {!!}

go-up-covers : (ζ : ℤ → 𝕀s) → (μ : ℤ → ℕ) → (n : ℤ)
             →        seq-of-sw-intervals (go-up μ ζ) n
               covers seq-of-sw-intervals          ζ  n 
go-up-covers ζ μ n = {!refl!}

-- Ternary boehm reals

TBR-to-sw-seq : 𝕋 → (ℤ → 𝕀s)
TBR-to-sw-seq (χ , b) n = χ n , n

TBR-to-sw-is-normalised : (χ : 𝕋) → is-normalised (TBR-to-sw-seq χ)
TBR-to-sw-is-normalised χ n = refl

normalised-nested-seq-yields-belowness : (χ : ℤ → 𝕀s) → is-normalised χ
                                       → sw-nested χ
                                       → (n : ℤ)
                                       → pr₁ (χ (succℤ n)) below pr₁ (χ n)
normalised-nested-seq-yields-belowness χ η = {!!}                           

belowness-yields-nested-seq : (χ : ℤ → 𝕀s)
                            → ((n : ℤ) → pr₁ (χ (succℤ n)) below pr₁ (χ n))
                            → sw-nested χ
belowness-yields-nested-seq = {!!}

normalised-seq-to-TBR : (χ : ℤ → 𝕀s) → is-normalised χ → sw-nested χ → 𝕋
normalised-seq-to-TBR χ η₁ η₂ = (pr₁ ∘ χ) , normalised-nested-seq-yields-belowness χ η₁ η₂

prenormalised-seq-to-TBR : (χ : ℤ → ℤ × ℤ) → is-prenormalised χ
                         → sw-nested χ → 𝕋
prenormalised-seq-to-TBR χ η₁ η₂ = normalised-seq-to-TBR (normalise χ η₁)
                                     (normalise-yields-normalised χ η₁)
                                     (normalise-preserves-nested χ η₁ η₂)

⟦_⟧' : 𝕋 → ℝ-d
⟦ χ  ⟧' = ⦅ seq-of-vw-intervals (seq-sw-to-vw (TBR-to-sw-seq χ)) ⦆
              (vw-intervalled-preserves (seq-sw-to-vw (TBR-to-sw-seq χ))
                (sw-is-intervalled (TBR-to-sw-seq χ)))
              (nested-gives-intersected (seq-of-vw-intervals (seq-sw-to-vw (TBR-to-sw-seq χ)))
                (belowness-yields-nested-seq (TBR-to-sw-seq χ) (pr₂ χ)))
              (sw-located-preserves (TBR-to-sw-seq χ)
                (normalised-is-located (TBR-to-sw-seq χ) (TBR-to-sw-is-normalised χ)))

-- Approximators and continuity oracles

map₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
     → (X → Y → Z) → Vec X n → Vec Y n → Vec Z n
map₂ f [] [] = []
map₂ f (x ∷ xs) (y ∷ ys) = f x y ∷ map₂ f xs ys

vec-satisfy : {X : 𝓤 ̇ } {n : ℕ} → (X → 𝓦 ̇ ) → Vec X n → 𝓦 ̇ 
vec-satisfy p [] = 𝟙
vec-satisfy p (x ∷ xs) = p x × vec-satisfy p xs

join' : 𝕀v → 𝕀s
join' z = go-up' (upValue (v-left z) (v-right z) (v-l≤r z)) (v-left z , v-prec z)

join : (ℤ → 𝕀v) → (ℤ → 𝕀s)
join = join' ∘_

vec-satisfy-preserved-by : {X : 𝓤 ̇ }
                         → {n : ℕ} (xs : Vec (ℤ → X) n) → (ks : Vec ℤ n) 
                         → (p : X → 𝓦 ̇ )
                         → vec-satisfy (λ x → ∀ (n : ℤ) → p (x n)) xs
                         → vec-satisfy p (map₂ id xs ks)
vec-satisfy-preserved-by [] [] p ⋆ = ⋆
vec-satisfy-preserved-by (x ∷ xs) (k ∷ ks) p (px , pxs)
 = px k , vec-satisfy-preserved-by xs ks p pxs

vec-lift : {X : 𝓤 ̇ } → (p : X → 𝓦 ̇ ) → Π p
         → {n : ℕ} → (xs : Vec X n) → vec-satisfy p xs
vec-lift p Πp [] = ⋆
vec-lift p Πp (x ∷ xs) = Πp x , vec-lift p Πp xs

vec-map-lift : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (p : X → 𝓦 ̇ ) (f : Y → X) → Π (p ∘ f)
             → {n : ℕ} → (ys : Vec Y n) → vec-satisfy p (vec-map f ys)
vec-map-lift p f Πpf [] = ⋆
vec-map-lift p f Πpf (y ∷ ys) = Πpf y , vec-map-lift p f Πpf ys

vec-map-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          → {n : ℕ} → (xs : Vec X n)
          → (f : X → Y) → (g : Y → Z)
          → vec-map (g ∘ f) xs ≡ vec-map g (vec-map f xs)
vec-map-≡ = {!!}

record FunctionMachine : 𝓤₁  ̇ where
  field
    d  : ℕ
    f  : Vec ℝ-d d → ℝ-d
    A  : Vec 𝕀v d → 𝕀v
    κ' : Vec 𝕋 d → ℤ → Vec ℤ d
    κ-is-coracle
      : (χs : Vec 𝕋 d) → (ϵ : ℤ)
      → pr₂ (join' (A (map₂ id (vec-map (seq-sw-to-vw ∘ TBR-to-sw-seq) χs) (κ' χs ϵ)))) ≥ ϵ
  f̂'  : Vec (ℤ → 𝕀v) d → (k : ℤ → Vec ℤ d) → (ℤ → 𝕀v)
  f̂'  χs k n = A (map₂ id χs (k n))
  f̂'' : Vec (ℤ → 𝕀s) d → (k : ℤ → Vec ℤ d) → (ℤ → 𝕀s)
  f̂'' χs k = join (f̂' (vec-map seq-sw-to-vw χs) k)
  κ'-is-coracle : (χs : Vec 𝕋 d) → is-prenormalised (f̂'' (vec-map TBR-to-sw-seq χs) (κ' χs))
  κ'-is-coracle χs ϵ = transport (λ ■ → ϵ ≤ pr₂ (join' (A (map₂ id ■ (κ' χs ϵ)))))
                         (vec-map-≡ χs TBR-to-sw-seq seq-sw-to-vw)
                         (κ-is-coracle χs ϵ)
  f̂   : Vec 𝕋 d → 𝕋
  f̂   χs   = prenormalised-seq-to-TBR (f̂'' (vec-map TBR-to-sw-seq χs) (κ' χs))
                 (κ'-is-coracle χs)
                 {!!}

Negation : FunctionMachine
FunctionMachine.d Negation = 1
FunctionMachine.f Negation [ x ] = ℝd- x
FunctionMachine.A Negation [ (((l , r) , i) , l≤r) ]
                           = ((ℤ- r , ℤ- l) , i) , ℤ≤-swap l r l≤r
FunctionMachine.κ' Negation _ _ = [ pos 0 ]
FunctionMachine.κ-is-coracle Negation χs ϵ = {!!}

𝕋-_ : 𝕋 → 𝕋
𝕋- x = FunctionMachine.f̂ Negation [ x ]
