
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
open import Todd.DyadicReals pe pt fe hiding (located)
open import Todd.TBRFunctions pt fe pe sq
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import Todd.TBRDyadicReals pt fe pe sq
open import Todd.upValue
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp renaming (_ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_ ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

_≡_ = Id

-- Dyadic interval properties and sequences

_covers_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇
(k , i) covers (c , j) = {!!}

intervalled nested located intersected : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
intervalled ζ = (n : ℤ) → pr₁ (ζ n) ≤ pr₂ (ζ n)
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
located     ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , (pr₂ (ζ n) - pr₁ (ζ n)) ≤ ϵ
intersected ζ = (n m : ℤ) → min (pr₂ (ζ n)) (pr₂ (ζ m)) ≤ max (pr₁ (ζ n)) (pr₁ (ζ m))

nested-gives-intersected : (ζ : ℤ → ℤ[1/2] × ℤ[1/2]) → nested ζ → intersected ζ
nested-gives-intersected ζ η n m = {!!}

⦅_⦆ : (ζ : ℤ → ℤ[1/2] × ℤ[1/2])
      → intervalled ζ → intersected ζ → located ζ
      → ℝ-d
⦅_⦆ = {!!}

l r : ℤ × ℤ → ℤ[1/2]
l (k , i) = quotient (k        , i)
r (k , i) = quotient (k +pos 2 , i)

-- Variable and specific width sequences

variable-width-interval : (ℤ × ℤ) × ℤ → ℤ[1/2] × ℤ[1/2]
variable-width-interval ((k , c) , i) = l (k , i) , l (c , i)

specific-width-interval :     ℤ × ℤ → ℤ[1/2] × ℤ[1/2]
specific-width-interval (k     , i) = l (k , i) , r (k , i)

sw-to-vw : (ℤ × ℤ) → (ℤ × ℤ) × ℤ
sw-to-vw (k , i) = (k , k +pos 2) , i

seq-sw-to-vw : (ℤ → ℤ × ℤ) → (ℤ → (ℤ × ℤ) × ℤ)
seq-sw-to-vw = sw-to-vw ∘_

seq-of-vw-intervals : (ℤ → (ℤ × ℤ) × ℤ) → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-vw-intervals = variable-width-interval ∘_

seq-of-sw-intervals : (ℤ →      ℤ × ℤ)  → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-sw-intervals = specific-width-interval ∘_

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

vw-intervalled vw-located : (ℤ → (ℤ × ℤ) × ℤ) → 𝓤₀ ̇ 
vw-intervalled ζ = (n : ℤ) → pr₁ (pr₁ (ζ n)) ≤ pr₂ (pr₁ (ζ n))
vw-located     ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , l (pr₂ (pr₁ (ζ n)) ℤ- pr₁ (pr₁ (ζ n)) , pr₂ (ζ n)) ≤ ϵ

vw-intervalled-preserves : seq-of-vw-intervals preserves vw-intervalled as intervalled
vw-intervalled-preserves ζ ρ n = pr₁ (ρ n) , ({!!} ∙ pr₂ (ρ n) ∙ {!!})

vw-located-preserves : seq-of-vw-intervals preserves vw-located as located
vw-located-preserves = {!!}

-- Specific width sequence properties

sw-is-intervalled : (ζ : ℤ → ℤ × ℤ) → vw-intervalled (seq-sw-to-vw ζ)
sw-is-intervalled ζ n = 2 , refl

sw-located : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
sw-located ζ = (ϵ : ℤ[1/2]) → Σ n ꞉ ℤ , l (pos 2 , pr₂ (ζ n)) ≤ ϵ

sw-located-preserves-vw : seq-sw-to-vw preserves sw-located as vw-located
sw-located-preserves-vw ζ ρ ϵ = {!!}

sw-located-preserves : seq-of-sw-intervals preserves sw-located as located
sw-located-preserves = preserves-trans _ _ _ _ located sw-located-preserves-vw vw-located-preserves

-- Prenormalised and normalised

is-normalised    : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
is-normalised    ζ = (n : ℤ) → pr₂ (ζ n) ≡ n

is-prenormalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-prenormalised ζ = (n : ℤ) → pr₂ (ζ n) ≥ n

normalised-implies-prenormalised : (ζ : ℤ → ℤ × ℤ)
                                 → is-normalised ζ
                                 → is-prenormalised ζ 
normalised-implies-prenormalised ζ ρ n = 0 , (ρ n ⁻¹)

go-up : (ℤ → ℕ) → (ζ : ℤ → ℤ × ℤ) → (ℤ → ℤ × ℤ)
go-up ρ ζ n = (upRight ^ k) (pr₁ (ζ n)) , pr₂ (ζ n) ℤ- pos k
 where k = ρ n

normalise : (ζ : ℤ → ℤ × ℤ) → is-prenormalised ζ → (ℤ → ℤ × ℤ)
normalise ζ ρ = go-up (λ n → pr₁ (ρ n)) ζ

normalise-yields-normalised : (ζ : ℤ → ℤ × ℤ) → (ρ : is-prenormalised ζ)
                            → is-normalised (normalise ζ ρ)
normalise-yields-normalised ζ ρ n
  = ap (_ℤ- pos k) (pr₂ (ρ n) ⁻¹)
  ∙ ℤ+-assoc _ _ _
  ∙ ap (n ℤ+_) (ℤ-sum-of-inverse-is-zero₀ k)
 where k = pr₁ (ρ n)

-- Normalised sequence properties

normalised-is-located : (ζ : ℤ → ℤ × ℤ) → (ρ : is-normalised ζ) → sw-located ζ
normalised-is-located ζ ρ ϵ = {!clog₂ ϵ!} , {!!}

normalise-preserves-nested : (ζ : ℤ → ℤ × ℤ) → (ρ : is-prenormalised ζ)
                           → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) ζ)
                           → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) (normalise ζ ρ))
normalise-preserves-nested = {!!}

go-up-covers : (ζ : ℤ → ℤ × ℤ) → (μ : ℤ → ℕ) → (n : ℤ)
             →        seq-of-sw-intervals (go-up μ ζ) n
               covers seq-of-sw-intervals          ζ  n 
go-up-covers ζ μ n = {!refl!}

-- Ternary boehm reals

TBR-to-sw-seq : 𝕋 → ℤ → ℤ × ℤ
TBR-to-sw-seq (χ , b) n = χ n , n

TBR-to-sw-is-normalised : (χ : 𝕋) → is-normalised (TBR-to-sw-seq χ)
TBR-to-sw-is-normalised χ n = refl

normalised-nested-seq-yields-belowness : (χ : ℤ → ℤ × ℤ) → is-normalised χ
                                       → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) χ) 
                                       → (n : ℤ) → pr₁ (χ (succℤ n)) below pr₁ (χ n)
normalised-nested-seq-yields-belowness χ η = {!!}                           

belowness-yields-nested-seq : (χ : ℤ → ℤ × ℤ)
                            → ((n : ℤ) → pr₁ (χ (succℤ n)) below pr₁ (χ n))
                            → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) χ) 
belowness-yields-nested-seq = {!!}

normalised-seq-to-TBR : (χ : ℤ → ℤ × ℤ) → is-normalised χ
                      → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) χ) → 𝕋
normalised-seq-to-TBR χ η₁ η₂ = (pr₁ ∘ χ) , normalised-nested-seq-yields-belowness χ η₁ η₂

prenormalised-seq-to-TBR : (χ : ℤ → ℤ × ℤ) → is-prenormalised χ
                         → nested ((seq-of-vw-intervals ∘ seq-sw-to-vw) χ)
                         → 𝕋
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

join : (ζ : ℤ → (ℤ × ℤ) × ℤ) → vw-intervalled ζ → ℤ → ℤ × ℤ
join ζ η = go-up (λ n → upValue (pr₁ (pr₁ (ζ n))) (pr₂ (pr₁ (ζ n))) (η n))
             (λ n → (pr₁ (pr₁ (ζ n))) , (pr₂ (ζ n)))

vec-satisfy-preserved-by : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec (ℤ → X) n) → (ks : Vec ℤ n) 
                         → (p : X → 𝓦 ̇ ) → vec-satisfy (λ x → ∀ (n : ℤ) → p (x n)) xs
                         → vec-satisfy p (map₂ id xs ks)
vec-satisfy-preserved-by [] [] p ⋆ = ⋆
vec-satisfy-preserved-by (x ∷ xs) (k ∷ ks) p (px , pxs) = px k , vec-satisfy-preserved-by xs ks p pxs

vec-lift : {X : 𝓤 ̇ } → (p : X → 𝓦 ̇ ) → Π p → {n : ℕ} → (xs : Vec X n) → vec-satisfy p xs
vec-lift p Πp [] = ⋆
vec-lift p Πp (x ∷ xs) = Πp x , vec-lift p Πp xs

vec-map-lift : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (p : X → 𝓦 ̇ ) (f : Y → X) → Π (p ∘ f)
             → {n : ℕ} → (ys : Vec Y n) → vec-satisfy p (vec-map f ys)
vec-map-lift p f Πpf [] = ⋆
vec-map-lift p f Πpf (y ∷ ys) = Πpf y , vec-map-lift p f Πpf ys

record FunctionMachine : 𝓤₁  ̇ where
  field
    n  : ℕ
    f  : Vec ℝ-d n → ℝ-d
    A  : Vec ((ℤ × ℤ) × ℤ) n → ((ℤ × ℤ) × ℤ)
    A-interval : ∀ xs → vec-satisfy (λ ((l , r) , i) → l ≤ r) xs → pr₁ (pr₁ (A xs)) ≤ pr₂ (pr₁ (A xs))
    κ' : Vec 𝕋 n → ℤ → Vec ℤ n
  f̂'  : Vec (ℤ → (ℤ × ℤ) × ℤ) n → (k : ℤ → Vec ℤ n) → (ℤ → (ℤ × ℤ) × ℤ)
  f̂'  χs k n = A (map₂ id χs (k n))
  f̂'-intervalled : (χs : Vec (ℤ → (ℤ × ℤ) × ℤ) n) → vec-satisfy vw-intervalled χs → (k : ℤ → Vec ℤ n)
                 → vw-intervalled (f̂' χs k) 
  f̂'-intervalled χs ηs k n = A-interval (map₂ (λ χᵢ → χᵢ) χs (k n))
                               (vec-satisfy-preserved-by χs (k n) (λ ((l , r) , i) → l ≤ r) ηs)
  f̂'' : Vec (ℤ → ℤ × ℤ)       n → (k : ℤ → Vec ℤ n) → (ℤ → ℤ × ℤ)
  f̂'' χs k = join (f̂' (vec-map seq-sw-to-vw χs) k)
                  (f̂'-intervalled _ (vec-map-lift vw-intervalled seq-sw-to-vw sw-is-intervalled χs) k)
  f̂   : Vec 𝕋 n → 𝕋
  f̂   χs     = prenormalised-seq-to-TBR (f̂'' (vec-map TBR-to-sw-seq χs) (κ' χs))
                 {!!} {!!}

Negation : FunctionMachine
FunctionMachine.n Negation = 1
FunctionMachine.f Negation (x ∷ []) = ℝd- x
FunctionMachine.A Negation (((l , r) , i) ∷ []) = ((ℤ- r , ℤ- l) , i)
FunctionMachine.A-interval Negation (((l , r) , i) ∷ []) (l≤r , ⋆) = ℤ≤-swap l r l≤r
FunctionMachine.κ' Negation _ _ = pos 0 ∷ []

𝕋-_ : 𝕋 → 𝕋
𝕋- x = FunctionMachine.f̂ Negation (x ∷ [])
