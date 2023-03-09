
\begin{code}

module CategoryTheory.Type where

open import MLTT.Spartan renaming (_∘_ to _∘'_)
open import UF.Subsingletons

record precategory {𝓤 𝓥 : Universe} : 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇ where
 field
  ob : 𝓤 ̇
  hom : (a b : ob) → 𝓥 ̇
  hom-set : ∀ {a} {b} → is-set (hom a b)
  u : {a : ob } → hom a a
  _∘_ : {a b c : ob} → hom  b c → hom a b → hom a c
  unit-l : {a b : ob} → (f : hom a b) → (u ∘ f) ＝ f
  unit-r : {a b : ob} → (f : hom a b) → (f ∘ u) ＝ f
  assoc : {a b c d : ob} → (f : hom a b) → (g : hom b c) → (h : hom c d) → (h ∘ (g ∘ f)) ＝ ((h ∘ g) ∘ f)

 type-of-object : (𝓤 ⁺) ̇
 type-of-object = type-of ob

 dom : {a b : ob} → hom a b → ob
 dom {a} {b} f = a

 codom : {a b : ob} → hom a b → ob
 codom {a} {b} f = b

 unit-l' : {a b : ob} → (f : hom a b) → f ＝ (u ∘ f)
 unit-l' {a} {b} f = unit-l f ⁻¹

_ᵒᵖ : precategory { 𝓤 } { 𝓥 } → precategory { 𝓤 } { 𝓥 }
record { ob      = ob ;
         hom     = hom ;
         hom-set = hom-set ;
         u       = u ;
         _∘_     = _∘_ ;
         unit-l  = unit-l ;
         unit-r  = unit-r ;
         assoc   = assoc    } ᵒᵖ

 = record
     { ob = ob
     ; hom = λ a b → hom b a
     ; hom-set = hom-set
     ; u = u
     ; _∘_ = λ a b → b ∘ a
     ; unit-l = unit-r
     ; unit-r = unit-l
     ; assoc = λ a b c → assoc c b a ⁻¹
     }

\end{code}

