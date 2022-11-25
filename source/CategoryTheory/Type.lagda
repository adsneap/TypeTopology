
\begin{code}

module CategoryTheory.Type where

open import MLTT.Spartan renaming (_∘_ to _∘'_)
open import UF.Subsingletons

record precategory : 𝓤ω where
 field
  ob : 𝓤 ̇
  hom : (a b : ob {𝓤}) → 𝓥 ̇
  hom-set : ∀ {a} {b} → is-set { 𝓥 } (hom { 𝓤 } { 𝓥 } a b)
  1ₐ : {a : ob {𝓤}} → hom {𝓤}{𝓥} a a
  _∘_ : {a b c : ob} → hom {𝓤}{𝓥} b c → hom {𝓤}{𝓥} a b → hom {𝓤}{𝓥} a c
  unit-l : {a b : ob} → (f : hom {𝓤}{𝓥} a b) → (1ₐ ∘ f) ＝ f
  unit-r : {a b : ob} → (f : hom {𝓤}{𝓥} a b) → (f ∘ 1ₐ) ＝ f
  assoc : {a b c d : ob} → (f : hom {𝓤}{𝓥} a b) → (g : hom b c) → (h : hom c d) → (h ∘ (g ∘ f)) ＝ ((h ∘ g) ∘ f)
 
 isomorphism : {a b : ob} → (f : hom a b) → 𝓦 ̇
 isomorphism {𝓤} {a} {b} f = Σ g ꞉ hom b a , (g ∘ f ＝ 1ₐ { 𝓤 }) × (f ∘ g ＝ 1ₐ { 𝓤 })

 isomorphism-is-prop : {a b : ob { 𝓤 }} → {f : hom a b} → is-prop (isomorphism f)
 isomorphism-is-prop {_} {_} {_} {f} (g , η , ε) (g' , η' , ε') = Σ-is-prop {!!} {!!} (g , η , ε) (g' , η' , ε') -- to-subtype-＝ (λ _ → ×-is-prop hom-set hom-set) g-equals-g'
  where
   g-equals-g' : g ＝ g'
   g-equals-g' = g              ＝⟨ unit-r g ⁻¹ ⟩
                 g ∘ 1ₐ         ＝⟨ ap (g ∘_) (ε' ⁻¹) ⟩
                 g ∘ (f ∘ g')   ＝⟨ assoc g' f g ⟩
                 (g ∘ f) ∘ g'   ＝⟨ ap (_∘ g') η ⟩
                 1ₐ ∘ g'        ＝⟨ unit-l g' ⟩
                 g'             ∎

 _≅_ : (a b : ob) → 𝓦 ̇
 a ≅ b = Σ f ꞉ hom a b , isomorphism f

 ≅-is-prop : {a b : ob} → is-prop (a ≅ b)
 ≅-is-prop  = Σ-is-prop (λ f g → {!!}) (λ _ → isomorphism-is-prop)
 
 isomorphism-is-set : {a b : ob { 𝓤 }} → is-set (a ≅ b) 
 isomorphism-is-set {_} {a} {b} x y = {!!}

 

 {-
 inverse : {a b : ob {𝓤}} → {f : hom a b} → isomorphism f → hom b a
 inverse (g , _ , _) = g

 inverse-iso : {a b : ob{𝓤}} {f : hom a b} → (i : _≅_ a b {f}) → _≅_ b a {inverse i}
 inverse-iso {_} {a} {b} {f} (g , η , ε) = f , ε , η

 object-type : ob → 𝓤 ̇
 object-type o = type-of o

module _
  (A : precategory)
 where

 open precategory A

 idtoiso : (a b : ob { 𝓤 })
         → (f : hom {_}{_} a b)
         → a ＝ b
         → _≅_ {_} a b { f }
 idtoiso a .a f refl = 1ₐ
                     , (ap (1ₐ ∘_) f-is-id ∙ unit-l 1ₐ)
                     , (ap (_∘ 1ₐ) f-is-id ∙ unit-l 1ₐ)
  where
   f-is-id : f ＝ 1ₐ
   f-is-id = {!!}
   te : (p : f ＝ 1ₐ) → (q : f ＝ 1ₐ) → p ＝ q
   te p q = (hom-set {_} {_} {a} {a}) p q

pSet : precategory
pSet = record
         { ob      = {!!}
         ; hom     = {!!}
         ; hom-set = {!!}
         ; 1ₐ      = id
         ; _∘_     = _∘'_
         ; unit-l  = {!!}
         ; unit-r  = {!!}
         ; assoc   = {!!}
         }
-}
{-
record category : {!!} where
 field
  pc : precategory
-}

   

\end{code}

