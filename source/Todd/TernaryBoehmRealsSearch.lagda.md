```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _+ℤ_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Todd.DyadicRationals
open import Todd.Prelude

module Todd.TernaryBoehmRealsSearch
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
  (dy : Dyadics)
  where

open import Todd.TernaryBoehmReals pt fe pe sq
open import Todd.FunctionEncodings pt fe pe sq dy hiding (r)

open set-quotients-exist sq
open Dyadics dy                                   
```

## Searchable types

Recall that in our general regression framework, we define searchable types as
follows:

```agda
decidable-predicate : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
decidable-predicate {𝓤} {𝓥} X
 = Σ p ꞉ (X → Ω 𝓥) , ((x : X) → decidable (pr₁ (p x)))

searchable : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → 𝓤 ⊔ 𝓥 ⁺ ̇ 
searchable {𝓤} {𝓥} X
 = Π (p , _) ꞉ decidable-predicate {𝓤} {𝓥} X
 , Σ x₀ ꞉ X , (Σ (pr₁ ∘ p) → pr₁ (p x₀))
```

We often search only uniformly continuous predicates, which are defined by using
closeness functions and then quotienting the type up to a certain closeness
function.

## Closeness function on 𝕋

For every discrete-sequence type `ℕ → X` (where `X` is discrete), we have a
canonical closeness function `c : (ℕ → X) × (ℕ → X) → ℕ∞`.

Recall that for `x,y : ℕ → X` and any `δ : ℕ`,

`c (x , y) ≼ ι δ ⇔ (x ≈ y) δ`,

where `c(x , y) : ℕ∞` is the value of the discrete-sequence closeness function
for `x` and `y`.

```
_≈'_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈' β) n = (i : ℕ) → i < n → α n ＝ β n
```

From the canonical closeness function on `ℕ → ℤ`, we can define one on `𝕋`:

```code
c : 𝕋 × 𝕋 → ℕ∞
c ((α , _) , (β , _)) = c (α ∘ pos , β ∘ pos)
```

Note that we only take into account positive precision-levels of  `x : 𝕋`; but,
as we already said, for our purposes of encoding real numbers, the information
kept in any `⟨ x ⟩ (pos n₁) : ℤ` includes the information kept in any
`⟨ x ⟩ (negsucc n₂) : ℤ`.

This closeness function, like that on signed-digits, gives the closeness of
*encodings* of real numbers; not the real numbers themselves.

## Predicates we wish to search

The above closeness function will give us a way to search uniformly continuous
decidable predicates on `𝕋`. These are those decidable predicates that can be
decided by only examining a finite portion of the location information held in
`𝕋`. We call the point `δ : ℤ` that we need to examine up to the "modulus of
continuity" of the predicate.

We could use the isomorphism between `𝕋` and `ℕ → 𝟛` to immediately give us a
searcher on such unifoormly continuous predicates using the below properties:

```agda
decidable-predicate⌜_,_⌝⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓤} {𝓦} X
                         → decidable-predicate {𝓥} {𝓦} Y
decidable-predicate⌜ e , (p , d) ⌝⁻¹ = (p ∘ ⌜ e ⌝⁻¹) , (d ∘ ⌜ e ⌝⁻¹)

decidable-predicate⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓥} {𝓦} Y
                         → decidable-predicate {𝓤} {𝓦} X
decidable-predicate⌜ e , (p , d) ⌝ = (p ∘ ⌜ e ⌝) , (d ∘ ⌜ e ⌝)

decidable-predicate⌜_,_⌝-correct
  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (e : X ≃ Y)
  → ((p , d) : decidable-predicate {𝓥} {𝓦} Y)
  → (y : Y) → pr₁ (p y)
  → pr₁ (pr₁ (decidable-predicate⌜ e , (p , d) ⌝) (⌜ e ⌝⁻¹ y))
decidable-predicate⌜ e , (p , d) ⌝-correct y
 = transport (λ - → pr₁ (p -)) (≃-sym-is-rinv e _ ⁻¹)
              
searchable⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                → searchable {𝓤} {𝓦} X
                → searchable {𝓥} {𝓦} Y
searchable⌜ e , 𝓔 ⌝ (p , d)
 = ⌜ e ⌝ (pr₁ p')
 , λ (y₀ , py₀) → pr₂ p' ((⌜ e ⌝⁻¹ y₀)
                , decidable-predicate⌜ e , (p , d) ⌝-correct y₀ py₀)
 where p' = 𝓔 (decidable-predicate⌜ e , (p , d) ⌝)
```

However, the searcher given by this isomorphism (like that on signed-digits)
would search the *entire* prefix of the stream from point `pos 0` to point
`pos δ`; despite the fact that the location information at `pos δ` *includes*
all of the location information previous to that.

Therefore, we prefer to use a different isomorphism: the one induced by the
`replace` function in Section IV.

## Searching quotiented encodings of compact intervals

First, we define the equivalence relation needed to determine uniformly
continuous decidable predicates on Ternary Boehm encodings of any compact
interval `⟪ k , i ⟫`.

This equivalence relation simply takes a modulus of continuity `δ : ℤ` and asks
if `⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ` given `x,y : CompactInterval (k , i)`.

```
CompEqRel : (δ : ℤ) ((k , i) : ℤ × ℤ) → EqRel {𝓤₀} {𝓤₀} (CompactInterval (k , i))
CompEqRel δ (k , i) = _≣≣_ , u , r , s , t
 where
   _≣≣_ : CompactInterval (k , i) → CompactInterval (k , i) → 𝓤₀ ̇ 
   (x ≣≣ y) = ⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ
   u : is-prop-valued _≣≣_
   u x y = ℤ-is-set
   r : reflexive _≣≣_
   r x = refl
   s : symmetric _≣≣_
   s x y = _⁻¹
   t : transitive _≣≣_
   t x y z = _∙_
```

Seen as we only need to look at level `δ : ℤ`, we can isolate the bricks on that
level into the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`.

Indeed, the quotient type `CompactInterval (k , i) / CompEqRel δ (k , i)` is
*equivalent* to the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`

```
Conv→ : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → CompactInterval (k , i) → ℤ[ lower (k , i) δ , upper (k , i) δ ]
Conv→ δ (k , i) x = ⟨ ι x ⟩ δ , ci-lower-upper (k , i) x δ

Conv← : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → ℤ[ lower (k , i) δ , upper (k , i) δ ] → CompactInterval (k , i)
Conv← δ (k , i) (z , l≤z≤u) = pr₁ (replace (k , i) (z , δ) l≤z≤u)

CompReplace : (δ : ℤ) ((k , i) : ℤ × ℤ)
            → (x : CompactInterval (k , i))
            → x ≈[ CompEqRel δ (k , i) ] (Conv← δ (k , i) ∘ Conv→ δ (k , i)) x
CompReplace δ (k , i) x = pr₂ (replace (k , i) (z , δ) l≤z≤u) ⁻¹
 where
   γ     = Conv→ δ (k , i) x
   z     = pr₁ γ
   l≤z≤u = pr₂ γ

Conv→-identifies-related-points
  : (δ : ℤ) → ((k , i) : ℤ × ℤ)
  → identifies-related-points {𝓤₀} {𝓤₀} {𝓤₀} {CompactInterval (k , i)}
      (CompEqRel δ (k , i)) (Conv→ δ (k , i))
Conv→-identifies-related-points δ (k , i)
 = to-subtype-＝ {𝓤₀} {𝓤₀} {ℤ} {λ z → lower (k , i) δ ≤ℤ z ≤ℤ upper (k , i) δ}
     (λ z → ≤ℤ²-is-prop {lower (k , i) δ} {upper (k , i) δ} z)

ℤ[_,_]-is-set : (a b : ℤ) → is-set (ℤ[ a , b ])
ℤ[ a , b ]-is-set = subsets-of-sets-are-sets ℤ (λ z → a ≤ℤ z ≤ℤ b)
                      ℤ-is-set (≤ℤ²-is-prop _)
                      
med-map/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → is-set A
         → (f : CompactInterval (k , i) → A)
         → identifies-related-points (CompEqRel δ (k , i)) f
         → CompactInterval (k , i) / CompEqRel δ (k , i) → A
med-map/ δ (k , i) s = mediating-map/ (CompEqRel δ (k , i)) s

uni-tri/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → (s : is-set A)
         → (f : CompactInterval (k , i) → A)
         → (p : identifies-related-points (CompEqRel δ (k , i)) f)
         → med-map/ δ (k , i) s f p ∘ η/ (CompEqRel δ (k , i)) ∼ f
uni-tri/ δ (k , i) s f p = universality-triangle/ (CompEqRel δ (k , i)) s f p

med-map : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → CompactInterval (k , i) / CompEqRel δ (k , i)
        → ℤ[ lower (k , i) δ , upper (k , i) δ ]
med-map δ (k , i) = med-map/ δ (k , i)
                      (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set)
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)

uni-tri : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → (med-map δ (k , i) ∘ η/ (CompEqRel δ (k , i))) ∼ Conv→ δ (k , i)
uni-tri δ (k , i) = uni-tri/ δ (k , i)
                      ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set 
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)
           
compact-equiv : (δ : ℤ) ((k , i) : ℤ × ℤ)
              → CompactInterval (k , i) / CompEqRel δ (k , i)
              ≃ ℤ[ lower (k , i) δ , upper (k , i) δ ]
compact-equiv δ (k , i) = f' , ((g' , fg) , (g' , gf))
 where
  f' : CompactInterval (k , i) / CompEqRel δ (k , i)
     → ℤ[ lower (k , i) δ , upper (k , i) δ ]
  f' = med-map δ (k , i)
  g' : ℤ[ lower (k , i) δ , upper (k , i) δ ]
     → CompactInterval (k , i) / CompEqRel δ (k , i)
  g' = η/ (CompEqRel δ (k , i)) ∘ Conv← δ (k , i)
  fg : f' ∘ g' ∼ id
  fg (z , l≤z≤u)
   = uni-tri δ (k , i) (Conv← δ (k , i) (z , l≤z≤u))
   ∙ to-subtype-＝ ≤ℤ²-is-prop (pr₂ (replace (k , i) (z , δ) l≤z≤u)) 
  gf : g' ∘ f' ∼ id
  gf = /-induction (CompEqRel δ (k , i)) (λ _ → /-is-set (CompEqRel δ (k , i)))
         (λ y → η/-identifies-related-points (CompEqRel δ (k , i))
           (ap (λ - → ⟨ ι (Conv← δ (k , i) -) ⟩ δ)
             (uni-tri δ (k , i) y)
           ∙ CompReplace δ (k , i) y ⁻¹))
```

This gives us a much more efficient searcher for Ternary Boehm reals in compact
intervals, because the searcher on finite subsets of `ℤ` does not need to check
every element of the `𝕋` sequence.

```
ℤ[_,_]-searchable' : (l u : ℤ) → (n : ℕ) → l +pos n ＝ u
                  → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , l ]-searchable' 0 refl (p , d)
 = ((l , ℤ≤-refl l , ℤ≤-refl l))
 , λ ((z , l≤z≤u) , pz)
   → transport (pr₁ ∘ p) (to-subtype-＝ ≤ℤ²-is-prop ((≤ℤ-antisym l z l≤z≤u) ⁻¹)) pz
ℤ[ l , .(succℤ (l +pos n)) ]-searchable' (succ n) refl (p , d)
 = Cases (d u*) (λ pu → u* , (λ _ → pu))
    (λ ¬pu → ans ,
      (λ ((z , l≤z , z≤u) , pz)
        → Cases (ℤ≤-split z u z≤u)
            (λ z<u → sol ((z , l≤z
                   , transport (z ≤_) (predsuccℤ _) (≤ℤ-back z u z<u))
                   , transport (pr₁ ∘ p) (to-subtype-＝ ≤ℤ²-is-prop refl) pz))
            (λ z＝u → 𝟘-elim (¬pu (transport (pr₁ ∘ p)
                                   (to-subtype-＝ ≤ℤ²-is-prop z＝u) pz)))))
 where
   u = succℤ (l +pos n)
   u* = u , (succ n , refl) , ℤ≤-refl u
   γ : ℤ[ l , l +pos n ] → ℤ[ l , u ]
   γ = ℤ[ l , l +pos n ]-succ
   IH = ℤ[ l , l +pos n ]-searchable' n refl ((p ∘ γ) , (d ∘ γ))
   ans = γ (pr₁ IH)
   sol = pr₂ IH

ℤ[_,_]-searchable : (l u : ℤ) → l ≤ u → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , u ]-searchable (n , p) = ℤ[ l , u ]-searchable' n p

𝕋-compact-searchable
  : ((k , i) : ℤ × ℤ) (δ : ℤ)
  → searchable {𝓤₀} {𝓦} (CompactInterval (k , i) / CompEqRel δ (k , i))
𝕋-compact-searchable (k , i) δ
 = searchable⌜ (≃-sym (compact-equiv δ (k , i)))
 , (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-searchable
     (lower≤upper (k , i) δ)) ⌝
```

Now we bring in our functions!

```
_≡_ = Id

record UniformContinuity (FM : FunctionMachine 1) : 𝓤₀ ̇  where
  open FunctionMachine FM
  field
    κ' : ℤ → ℤ
    κ'-is-ucoracle
      : {(k , i) : 𝕀s}
      → (χ : CompactInterval (k , i)) → (ϵ : ℤ)
      → pr₂ (join' (A [ ((seq-sw-to-vw ∘ TBR-to-sw-seq) (ι χ) (κ' ϵ)) ]))
      ≥ ϵ
    κ'-relates-to-κ
      : {(k , i) : 𝕀s}
      → (χ : CompactInterval (k , i)) → (ϵ : ℤ)
      → upRight-𝕀s (pr₁ (κ'-is-ucoracle χ ϵ))     (f̂'' [ TBR-to-sw-seq (ι χ) ] (λ - → [ κ' - ]) ϵ)
      ≡ upRight-𝕀s (pr₁ (κ-is-coracle [ ι χ ] ϵ)) (f̂'' [ TBR-to-sw-seq (ι χ) ] (κ [ ι χ ])      ϵ)

module SearchContinuity (FM : FunctionMachine 1) (UC : UniformContinuity FM) where

  open FunctionMachine FM
  open UniformContinuity UC

  Lem-628 : (χ γ : 𝕋) (ϵ : ℤ) → let (δχ , δγ) = (head (κ [ χ ] ϵ) , head (κ [ γ ] ϵ) ) in 
            δχ ≡ δγ
          → ⟨ χ ⟩ δχ ≡ ⟨ γ ⟩ δγ
          → ⟨ f̂ [ χ ] ⟩ ϵ ≡ ⟨ f̂ [ γ ] ⟩ ϵ
  Lem-628 χ γ ϵ δχ≡δγ χδ≡γδ = ap pr₁ seven
   where
     δχ = head (κ [ χ ] ϵ)
     δγ = head (κ [ γ ] ϵ)
     one : A [ sw-to-vw (⟨ χ ⟩ δχ , δχ) ] ≡ A [ sw-to-vw (⟨ γ ⟩ δγ , δγ) ]
     one = ap (A ∘ [_] ∘ sw-to-vw) (ap₂ _,_ χδ≡γδ δχ≡δγ)
     two : join' (A [ sw-to-vw (⟨ χ ⟩ δχ , δχ) ]) ≡ join' (A ([ sw-to-vw (⟨ γ ⟩ δγ , δγ) ]))
     two = ap join' one
     two' : join' (A (vec-map₂ [ ((seq-sw-to-vw ∘ TBR-to-sw-seq) χ) ] (κ [ χ ] ϵ)))
          ≡ join' (A (vec-map₂ [ ((seq-sw-to-vw ∘ TBR-to-sw-seq) γ) ] (κ [ γ ] ϵ)))
     two' = ap (join' ∘ A) (map₂-get _ _) ∙ two ∙ ap (join' ∘ A) (map₂-get _ _ ⁻¹) 
     three : f̂'' [ TBR-to-sw-seq χ ] (κ [ χ ]) ϵ ≡  f̂'' [ TBR-to-sw-seq γ ] (κ [ γ ]) ϵ
     three = two'
     seven : upRight-𝕀s (pr₁ (κ-is-coracle [ χ ] ϵ)) (f̂'' [ TBR-to-sw-seq χ ] (κ [ χ ]) ϵ)
           ≡ upRight-𝕀s (pr₁ (κ-is-coracle [ γ ] ϵ)) (f̂'' [ TBR-to-sw-seq γ ] (κ [ γ ]) ϵ)
     seven = ap₂ upRight-𝕀s (≥-lemma _ _ ϵ (ap pr₂ three) (κ-is-coracle [ χ ] ϵ) (κ-is-coracle [ γ ] ϵ)) three

  Lem-629 : {(k , i) : ℤ × ℤ}
          → (χ γ : CompactInterval (k , i)) (ϵ : ℤ)
          → ⟨ ι χ ⟩ (κ' ϵ) ≡ ⟨ ι γ ⟩ (κ' ϵ)
          → ⟨ f̂ [ ι χ ] ⟩ ϵ ≡ ⟨ f̂ [ ι γ ] ⟩ ϵ
  Lem-629 χ γ ϵ χδ≡γδ = ap pr₁ seven
   where
     δ = κ' ϵ
     one : A [ sw-to-vw (⟨ ι χ ⟩ δ , δ) ] ≡ A [ sw-to-vw (⟨ ι γ ⟩ δ , δ) ]
     one = ap (A ∘ [_] ∘ sw-to-vw) (ap₂ _,_ χδ≡γδ refl)
     two : join' (A [ sw-to-vw (⟨ ι χ ⟩ δ , δ) ]) ≡ join' (A ([ sw-to-vw (⟨ ι γ ⟩ δ , δ) ]))
     two = ap join' one
     two' : join' (A (vec-map₂ [ ((seq-sw-to-vw ∘ TBR-to-sw-seq) (ι χ)) ] [ δ ]))
          ≡ join' (A (vec-map₂ [ ((seq-sw-to-vw ∘ TBR-to-sw-seq) (ι γ)) ] [ δ ]))
     two' = ap (join' ∘ A) (map₂-get [ (seq-sw-to-vw ∘ TBR-to-sw-seq) (ι χ) ] [ δ ])
          ∙ two
          ∙ ap (join' ∘ A) (map₂-get [ (seq-sw-to-vw ∘ TBR-to-sw-seq) (ι γ) ] [ δ ] ⁻¹) 
     three : f̂'' [ TBR-to-sw-seq (ι χ) ] (λ - → [ κ' - ]) ϵ ≡  f̂'' [ TBR-to-sw-seq (ι γ) ] (λ - → [ κ' - ]) ϵ
     three = two'
     six : upRight-𝕀s (pr₁ (κ'-is-ucoracle χ ϵ)) (f̂'' [ TBR-to-sw-seq (ι χ) ] (λ - → [ κ' - ]) ϵ)
         ≡ upRight-𝕀s (pr₁ (κ'-is-ucoracle γ ϵ)) (f̂'' [ TBR-to-sw-seq (ι γ) ] (λ - → [ κ' - ]) ϵ)
     six = ap₂ upRight-𝕀s (≥-lemma _ _ ϵ (ap pr₂ three) (κ'-is-ucoracle χ ϵ) (κ'-is-ucoracle γ ϵ)) three
     seven : upRight-𝕀s (pr₁ (κ-is-coracle [ ι χ ] ϵ)) (f̂'' [ TBR-to-sw-seq (ι χ) ] (κ [ ι χ ]) ϵ)
           ≡ upRight-𝕀s (pr₁ (κ-is-coracle [ ι γ ] ϵ)) (f̂'' [ TBR-to-sw-seq (ι γ) ] (κ [ ι γ ]) ϵ)
     seven = κ'-relates-to-κ χ ϵ ⁻¹ ∙ six ∙ κ'-relates-to-κ γ ϵ

  𝕋¹-uc-predicate : (𝕋 → Ω 𝓦) → 𝓦 ̇
  𝕋¹-uc-predicate {𝓦} p
   = Σ δ ꞉ ℤ
   , ((χ γ : 𝕋)
     → ⟨ χ ⟩ δ ≡ ⟨ γ ⟩ δ
     → p χ holds ⇔ p γ holds)

  𝕋¹-uc-predicate-ki : ((k , i) : ℤ × ℤ)
                     → (CompactInterval (k , i) → Ω 𝓦)
                     → 𝓦 ̇
  𝕋¹-uc-predicate-ki (k , i) p
   = Σ δ ꞉ ℤ
   , ((χ γ : CompactInterval (k , i))
     → ⟨ ι χ ⟩ δ ≡ ⟨ ι γ ⟩ δ
     → p χ holds ⇔ p γ holds)

  𝕋¹-uc-predicate-equiv
   : {k i : ℤ} → (p : CompactInterval (k , i) → Ω 𝓦)
   → ((δ , _) : 𝕋¹-uc-predicate-ki (k , i) p)
   → ∃! p* ꞉ (CompactInterval (k , i) / CompEqRel δ (k , i) → Ω 𝓦)
   , p* ∘ η/ (CompEqRel δ (k , i)) ∼ p
  𝕋¹-uc-predicate-equiv {𝓦} {k} {i} p (δ , ϕ)
   = /-universality (CompEqRel δ (k , i))
      (Ω-is-set (fe 𝓦 𝓦) (pe 𝓦))
      p
      (λ ≡δ → Ω-extensionality (fe 𝓦 𝓦) (pe 𝓦)
                (pr₁ (ϕ _ _ ≡δ))
                (pr₂ (ϕ _ _ ≡δ)))

  p∘-is-uc : {(k , i) : 𝕀s} (p : 𝕋 → Ω 𝓦)
           → 𝕋¹-uc-predicate {𝓦} p
           → 𝕋¹-uc-predicate-ki {𝓦} (k , i) (p ∘ f̂ ∘ [_] ∘ ι)
  p∘-is-uc p (δ , ϕ)
    = κ' δ
    , λ χ γ χδ≡γδ → ϕ _ _ (Lem-629 χ γ δ χδ≡γδ)
```
-- Therefore any 𝕋¹-uc-predicate can be searched
