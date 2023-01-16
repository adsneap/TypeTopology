\begin{code}

open import MLTT.Spartan renaming (_∘_ to _∘'_)
open import CategoryTheory.Type
open import CategoryTheory.CatType
open import CategoryTheory.Properties
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import UF.Equiv hiding (_≅_)
open import UF.Retracts
open import UF.Base

module CategoryTheory.Examples where

module Discrete
  (A : 𝓤 ̇)
  (A-is-1-type : (x y : A) → is-set (x ＝ y))
 where

 pcDiscrete : precategory { 𝓤 }
 pcDiscrete = record
                { ob = A
                ; hom = λ a b → a ＝ b
                ; hom-set = λ p q → A-is-1-type _ _ p q
                ; u = refl
                ; _∘_ = λ e₁ e₂ → e₂ ∙ e₁
                ; unit-l = λ f → refl-right-neutral f ⁻¹
                ; unit-r = λ f → refl-left-neutral
                ; assoc = λ f g h → ∙assoc f g h
                }

 id-to-iso : {a b : A} → a ＝ b → _≅_ 𝓤 pcDiscrete a b
 id-to-iso e = e , ((e ⁻¹) , (right-inverse e ⁻¹)  , left-inverse e)

 iso-to-id : {a b : A} → _≅_ 𝓤 pcDiscrete a b → a ＝ b
 iso-to-id {a} {b} (f , _) = f

 comp1 : {a b : A} (x : _≅_ 𝓤 pcDiscrete a b) → id-to-iso (iso-to-id x) ＝ x
 comp1 {a} {.a} (refl , refl , refl , refl) = refl

 comp2 : {a b : A} → (x : a ＝ b) → iso-to-id (id-to-iso x) ＝ x
 comp2 {a} {b} _ = refl

 id-to-iso-has-section : {a b : A} → has-section (id-to-iso {a} {b})
 id-to-iso-has-section {a} {b} = iso-to-id , comp1

 id-to-iso-is-section : {a b : A} → is-section (id-to-iso {a} {b})
 id-to-iso-is-section {a} {b} = iso-to-id , comp2

 id-to-iso-is-equiv : {a b : A} → is-equiv (id-to-iso {a} {b})
 id-to-iso-is-equiv {a} {b} = id-to-iso-has-section , id-to-iso-is-section

 cDiscrete : category pcDiscrete
 cDiscrete = record { idtoiso-is-equiv = id-to-iso , id-to-iso-is-equiv }

module Set where
 
 pcSet : FunExt → precategory {𝓤 ⁺}
 pcSet {𝓤} fe = record
              { ob = hSet 𝓤
              ; hom = λ (A , _) (B , _) → A → B
              ; hom-set = λ { {(A , A-is-set)} {B , B-is-set} → Π-is-set (fe 𝓤 𝓤) λ _ → B-is-set }
              ; u = id
              ; _∘_ = _∘'_
              ; unit-l = λ _ → refl
              ; unit-r = λ _ → refl
              ; assoc = λ _ _ _ → refl
              }
 module _
  (ua : is-univalent 𝓤)
  (fe : FunExt)
   where

  {-

  jjjj : {(a , a-is-set) (b , b-is-set) : hSet 𝓤}
       → is-equiv (idtoeq a b)
  jjjj {a , a-is-set} {b , b-is-set} = ua a b

  whatthis : {(a , a-is-set) (b , b-is-set) : hSet 𝓤} → a ≃ b
  whatthis = {!!}

  ≃-to-≅ : {(a , a-is-set) (b , b-is-set) : hSet 𝓤} → a ≃ b → _≅_ (𝓤 ⁺) (pcSet fe) (a , a-is-set) (b , b-is-set)
  ≃-to-≅ {a , a-is-set} {b , b-is-set} (f , (g , hs) , g' , is) = f , g , {!!} , {!!}

  -}

  idtoiso-Set : {a b : hSet 𝓤} → a ＝ b → _≅_ (𝓤 ⁺) (pcSet fe) a b
  idtoiso-Set refl = id , id , refl , refl

  idtoiso-Set' : {(a , _) (b , _) : hSet 𝓤} → a ＝ b → a ≃ b
  idtoiso-Set' refl = ≃-refl _
  
  isotoid-Set : {a b : hSet 𝓤}  → _≅_ (𝓤 ⁺) (pcSet fe) a b → a ＝ b
  isotoid-Set {a , a-is-set} {b , b-is-set} (f , g , gf , fg) = to-Σ-＝ (II , being-set-is-prop (fe 𝓤 𝓤) (transport is-set II a-is-set) b-is-set)
   where
    I : is-equiv (idtoeq a b)
    I = ua a b
    II : a ＝ b
    II = eqtoid ua a b (f , (g , λ x → ap (λ id → id x) fg)
                          ,  g , λ x → ap (λ id → id x) gf)
 
  Setcomp1 : {a b : hSet 𝓤} → (iso : _≅_ (𝓤 ⁺) (pcSet fe) a b)
           → idtoiso-Set {a} {b} (isotoid-Set iso) ＝ iso
  Setcomp1 {a , a-is-set} {b , b-is-set} (f , g , fg , gf) = {!!}

  Setcomp2 : {a b : hSet 𝓤} → (x : a ＝ b) → isotoid-Set (idtoiso-Set x) ＝ x
  Setcomp2 {a , a-is-set} {.a , .a-is-set} refl = {!!}
   where
    γ : isotoid-Set { a , a-is-set } (((λ x → x) , (λ x → x) , refl , refl)) ＝ refl
    γ = {!!}

  idtoiso-Set-has-section : {a b : hSet 𝓤} → has-section (idtoiso-Set {a} {b})
  idtoiso-Set-has-section {a} {b} = isotoid-Set , Setcomp1

  idtoiso-Set-is-section : {a b : hSet 𝓤} → is-section (idtoiso-Set {a} {b})
  idtoiso-Set-is-section {a} {b} = isotoid-Set , Setcomp2

  idtoiso-Set-is-equiv : {a b : hSet 𝓤} → is-equiv (idtoiso-Set {a} {b})
  idtoiso-Set-is-equiv {a} {b} = idtoiso-Set-has-section , idtoiso-Set-is-section

  univalent-set-satisfies-equivalence : {a b : hSet 𝓤} → (a ＝ b) ≃ _≅_ (_ ⁺) (pcSet fe) a b
  univalent-set-satisfies-equivalence = idtoiso-Set , idtoiso-Set-is-equiv

  cSet : (fe : FunExt)
       → is-univalent (𝓤 ⁺)
       → category {𝓤 ⁺} { _ } (pcSet fe)
  cSet fe u = record { idtoiso-is-equiv = univalent-set-satisfies-equivalence
                     }

module Preorder
 (A : 𝓤 ̇)
 (_≤_ : A → A → 𝓥 ̇)
 (≤-is-prop : ∀ {a} {b} → is-prop (a ≤ b))
 (≤-reflexive : ∀ {a} → a ≤ a)
 (≤-transitive : ∀ {a} {b} {c} → a ≤ b → b ≤ c → a ≤ c)
   where

 pcPreorder : precategory { 𝓤 }
 pcPreorder = record
                { ob = A
                ; hom = _≤_
                ; hom-set = props-are-sets ≤-is-prop
                ; u = ≤-reflexive
                ; _∘_ = λ l₁ l₂ → ≤-transitive l₂ l₁
                ; unit-l = λ f → ≤-is-prop (≤-transitive f ≤-reflexive) f
                ; unit-r = λ f → ≤-is-prop (≤-transitive ≤-reflexive f) f
                ; assoc = λ f g h →
                              ≤-is-prop (≤-transitive (≤-transitive f g) h)
                              (≤-transitive f (≤-transitive g h))
                }
 module _
  (A-is-set : is-set A)
  (≤-anti : ∀ a b → a ≤ b → b ≤ a → a ＝ b)
   where

  idtoiso-≤ : {a b : A} → a ＝ b → _≅_ 𝓤 pcPreorder a b
  idtoiso-≤ {a} {.a} refl = ≤-reflexive , ≤-reflexive , ≤-is-prop _ _ , ≤-is-prop _ _

  isotoid-≤ : {a b : A} → _≅_ 𝓤 pcPreorder a b → a ＝ b
  isotoid-≤ {a} {b} (l , l' , _) = ≤-anti a b l l'

  ≤-comp1 : {a b : A} → (eq : _≅_ 𝓤 pcPreorder a b) → idtoiso-≤ (isotoid-≤ eq) ＝ eq 
  ≤-comp1 {a} {b} (a≤b , b≤a , c1 , c2) = to-subtype-＝ (λ _ → isomorphism-is-prop 𝓤 pcPreorder) (≤-is-prop (pr₁ (idtoiso-≤ (≤-anti a b a≤b b≤a))) a≤b)

  ≤-comp2 : {a b : A} → (e : a ＝ b) → isotoid-≤ (idtoiso-≤ e) ＝ e
  ≤-comp2 {a} refl = A-is-set (≤-anti a a ≤-reflexive ≤-reflexive) refl
  
  idtoiso-≤-has-section : {a b : A} → has-section (idtoiso-≤ {a} {b})
  idtoiso-≤-has-section {a} {b} = isotoid-≤ , ≤-comp1

  idtoiso-≤-is-section : {a b : A} → is-section (idtoiso-≤ {a} {b})
  idtoiso-≤-is-section {a} {b} = isotoid-≤ , ≤-comp2
 
  idtoiso-≤-is-equiv : {a b : A} → is-equiv (idtoiso-≤ {a} {b})
  idtoiso-≤-is-equiv {a} {b} = idtoiso-≤-has-section , idtoiso-≤-is-section

  partial-order-satisfies-equivalence : {a b : A} → (a ＝ b) ≃ _≅_ 𝓤 pcPreorder a b
  partial-order-satisfies-equivalence {a} {b} = idtoiso-≤ , idtoiso-≤-is-equiv

  cpartialorder : category pcPreorder
  cpartialorder = record { idtoiso-is-equiv = partial-order-satisfies-equivalence
                         }

\end{code}
