\begin{code}

module CategoryTheory.CatType where

open import MLTT.Spartan renaming (_∘_ to _∘'_)
open import UF.Subsingletons
open import CategoryTheory.Type
open import CategoryTheory.Properties
open import UF.Univalence
open import UF.Equiv hiding (_≅_)
open import UF.Base

record category {𝓤 𝓥 : Universe} (pC : precategory {𝓤} {𝓥}) : 𝓤 ⊔ 𝓥 ̇ where
 open precategory {𝓤} {𝓥} pC 
 field
  idtoiso-is-equiv : {a b : ob} → (a ＝ b) ≃ (_≅_ 𝓤 pC a b)

module _
  (𝓤 : Universe)
  (pC : precategory {𝓤} {𝓥})
  (C : category pC)
 where
 
 open precategory pC
 open category C

 isotoid : {a b : ob} → _≅_ 𝓤 pC a b → a ＝ b
 isotoid iso = back-eqtofun idtoiso-is-equiv iso

 object-type-is-set : {X Y : ob} → is-set (X ＝ Y)
 object-type-is-set {X} {Y} = equiv-to-set idtoiso-is-equiv (isomorphism-is-set 𝓤 pC)
 
 not-sure : {a a' b b' : ob} {f : hom a b} {p : a ＝ a'} {q : b ＝ b'} → transport₂ hom p q f ＝ (pr₁ (idtoiso 𝓤 pC q) ∘ f) ∘ (pr₁ (idtoiso 𝓤 pC (p ⁻¹)))
 not-sure {_} {_} {_} {_} {f} {refl} {refl} = unit-r f ⁻¹ ∙ ap (_∘ u) (unit-l f ⁻¹)

 idtoiso-inverse : {a a' : ob} {p : a ＝ a'} → idtoiso 𝓤 pC (p ⁻¹) ＝ ! 𝓤 pC (idtoiso 𝓤 pC p)
 idtoiso-inverse {_} {_} {refl} = to-subtype-＝ (λ _ → isomorphism-is-prop 𝓤 pC) refl

 idtoiso-comp : {a b c : ob} {p : a ＝ b} {q : b ＝ c} → idtoiso 𝓤 pC (p ∙ q) ＝ _≅∘_ 𝓤 pC (idtoiso 𝓤 pC p) (idtoiso 𝓤 pC q)
 idtoiso-comp {_} {_} {_} {refl} {refl} = to-subtype-＝ (λ _ → isomorphism-is-prop 𝓤 pC) (unit-l u ⁻¹)

 {- Works but not satisfied with it
 idtoiso-comp' : {a b c : ob} {f : _≅_ 𝓤 pC a b} {e : _≅_ 𝓤 pC b c} → isotoid (_≅∘_ 𝓤 pC f e) ＝ isotoid f ∙ isotoid e
 idtoiso-comp' {_} {_} {_} {f , f' , e₁ , e₂} {g , g' , e₃ , e₄} = refl-is-set ob P (isotoid ((𝓤 ≅∘ pC) (f , f' , e₁ , e₂) (g , g' , e₃ , e₄))) (isotoid (f , f' , e₁ , e₂) ∙ isotoid (g , g' , e₃ , e₄))
  where
   P : (x : ob) (p : x ＝ x) → p ＝ refl
   P x refl = refl
 -}

 
  
\end{code}
