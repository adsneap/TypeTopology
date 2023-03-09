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

pc𝟘 : precategory { 𝓤 } { 𝓥 }
pc𝟘 = record
        { ob      = 𝟘
        ; hom     = λ x y → 𝟘-elim x
        ; hom-set = λ {a} → 𝟘-elim a
        ; u       = λ {a} → 𝟘-elim a
        ; _∘_     = λ {a} → 𝟘-elim a
        ; unit-l  = λ {a} → 𝟘-elim a
        ; unit-r  = λ {a} → 𝟘-elim a
        ; assoc   = λ {a} → 𝟘-elim a
        }

c𝟘 : category { 𝓤 } { 𝓥 } pc𝟘
c𝟘 = record { idtoiso-is-equiv = λ {a} → 𝟘-elim a }

open import MLTT.Unit-Properties
open import UF.Subsingletons

module Discrete
  (A : 𝓤 ̇)
  (A-is-1-type : (x y : A) → is-set (x ＝ y))
 where

 pcDiscrete : precategory { 𝓤 }
 pcDiscrete = record
                { ob      = A
                ; hom     = λ a b → a ＝ b
                ; hom-set = λ p q → A-is-1-type _ _ p q
                ; u       = refl
                ; _∘_     = λ e₁ e₂ → e₂ ∙ e₁
                ; unit-l  = λ f → refl-right-neutral f ⁻¹
                ; unit-r  = λ f → refl-left-neutral
                ; assoc   = λ f g h → ∙assoc f g h
                }

 id-to-iso : {a b : A} → a ＝ b → _≅_ 𝓤 pcDiscrete a b
 id-to-iso e = e , ((e ⁻¹) , (right-inverse e ⁻¹)  , left-inverse e)

 iso-to-id : {a b : A} → _≅_ 𝓤 pcDiscrete a b → a ＝ b
 iso-to-id {a} {b} (f , _) = f

 comp1 : {a b : A} (x : _≅_ 𝓤 pcDiscrete a b) → (id-to-iso ∘' iso-to-id) x ＝ id x
 comp1 {a} {.a} (refl , refl , refl , refl) = refl

 comp2 : {a b : A} → (x : a ＝ b) → (iso-to-id ∘' id-to-iso) x ＝ x
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

  univalence-says : {A B : hSet 𝓤} → Σ (λ x → is-section (idtoeq (pr₁ A) (pr₁ B)))
  univalence-says {A , A-is-set} {B , B-is-set} = ua A B
 
  {-
  eq-to-id : {(A , A-is-set) (B , B-is-set) : hSet 𝓤} → A ≃ B → A ＝ B
  eq-to-id = eqtoid ua _ _

  eqtoiso : {(A , A-is-set) (B , B-is-set) : hSet 𝓤} → A ≃ B
                                                     → _≅_ (𝓤 ⁺) (pcSet fe) (A , A-is-set) (B , B-is-set)
  eqtoiso {A , A-is-set} {B , B-is-set} eq =
   idtoiso (𝓤 ⁺) (pcSet fe) (to-subtype-＝ {𝓤 ⁺} { 𝓤 } { 𝓤 ̇ } { is-set } { A } { B } { A-is-set } { B-is-set }
                             (λ U → being-set-is-prop (fe 𝓤 𝓤)) II)
   where
    II : A ＝ B
    II = eqtoid ua A B eq -- eq

  isotoeq : {(A , A-is-set) (B , B-is-set) : hSet 𝓤} → _≅_ (𝓤 ⁺) (pcSet fe) (A , A-is-set) (B , B-is-set) → A ≃ B 
  isotoeq {A , A-is-set} {B , B-is-set} (f , g , gf , fg) = f , ((g , λ x → ap (λ id → id x) fg) ,
                                                                  g , λ x → ap (λ id → id x) gf)

  idtoiso-Set : {a b : hSet 𝓤} → a ＝ b → _≅_ (𝓤 ⁺) (pcSet fe) a b
  idtoiso-Set = {!!}

  isotoid-Set : {a b : hSet 𝓤}  → _≅_ (𝓤 ⁺) (pcSet fe) a b → a ＝ b
  isotoid-Set {a , a-is-set} {b , b-is-set} (f , g , gf , fg) = {!!}

  Setcomp1 : {a b : hSet 𝓤} → (iso : _≅_ (𝓤 ⁺) (pcSet fe) a b)
           → idtoiso-Set {a} {b} (isotoid-Set iso) ＝ iso
  Setcomp1 = {!!}

  Setcomp2 : {a b : hSet 𝓤} → (x : a ＝ b) → isotoid-Set (idtoiso-Set x) ＝ x
  Setcomp2 = {!!}

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
  cSet fe u = record { idtoiso-is-equiv = univalent-set-satisfies-equivalence }
  -}
  {-
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

  -- _≅_ ≃ _≃_ (for set)
  -- _≃_ ≃ _=_
  
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
  -}

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
-- Fundamental Pregroupoid Category

module FP 
  (X : 𝓤 ̇)
 where

 open import UF.PropTrunc

 module _
   (pt : propositional-truncations-exist)
  where

  open PropositionalTruncation pt
 
  pcFP : precategory
  pcFP = record
           { ob = X
           ; hom = λ a b → ∥ a ＝ b ∥
           ; hom-set = props-are-sets ∥∥-is-prop
           ; u = ∣ refl ∣
           ; _∘_ = λ f g → ∥∥-functor₂ (λ u v → v ∙ u) f g
           ; unit-l = λ f → ∥∥-is-prop (∥∥-functor₂ (λ u v → v ∙ u) ∣ refl ∣ f) f
           ; unit-r = λ f → ∥∥-is-prop (∥∥-functor₂ (λ u v → v ∙ u) f ∣ refl ∣) f
           ; assoc = λ f g h → ∥∥-is-prop (∥∥-functor₂ (λ u v → v ∙ u) h (∥∥-functor₂ (λ u v → v ∙ u) g f))
                                          (∥∥-functor₂ (λ u v → v ∙ u) (∥∥-functor₂ (λ u v → v ∙ u) h g) f)
           }

-- Homotopy Precategory Of Types

module HP
  (𝓤 : Universe)
 where
 
 open import UF.PropTrunc

 module _
   (pt : propositional-truncations-exist)
  where

  open PropositionalTruncation pt

  hpPC : precategory
  hpPC = record
           { ob = 𝓤 ̇
           ; hom = λ X Y → ∥ (X → Y) ∥
           ; hom-set = props-are-sets ∥∥-is-prop
           ; u = ∣ id ∣
           ; _∘_ = ∥∥-functor₂ _∘'_
           ; unit-l = λ f → ∥∥-is-prop (∥∥-functor₂ _∘'_ ∣ id ∣ f) f
           ; unit-r = λ f → ∥∥-is-prop (∥∥-functor₂ _∘'_ f ∣ id ∣) f
           ; assoc = λ f g h → ∥∥-is-prop (∥∥-functor₂ _∘'_ h (∥∥-functor₂ _∘'_ g f))
                                         (∥∥-functor₂  _∘'_ (∥∥-functor₂ _∘'_ h g) f)
           }


-- Rel

{-
module Rel where

 open import UF.PropTrunc

 module _
   (pt : propositional-truncations-exist)
  where

  open PropositionalTruncation pt
  open import UF.Powerset

  RelPC : precategory { 𝓤 ⁺ }
  RelPC {𝓤} = record
            { ob      = hSet 𝓤 
            ; hom     = λ (A , _) (B , _) → A → B → 𝓤 ̇
            ; hom-set = λ {(A , A-is-set)} {(B , B-is-set)} p q → {!!}
            ; u       = λ {(A , A-is-set)} → λ a b → a ＝ b
            ; _∘_     = λ {(A , A-is-set) (B , B-is-set) (C , C-is-set)} f g a c → ∥ (Σ b ꞉ B , f b c × g a b) ∥
            ; unit-l  = λ f → {!!}
            ; unit-r  = λ f → {!!}
            ; assoc   = λ f g h → {!!}
            }
-}

module Slice
  (pC : precategory { 𝓤 } { 𝓥 })
  (C : category pC)
  (A : precategory.ob pC)
 where
  open precategory pC
  open category C

  Slice-ob : 𝓤 ⊔ 𝓥 ̇
  Slice-ob = Σ B ꞉ ob , hom A B

  Slice-hom : Slice-ob
            → Slice-ob
            → 𝓥 ̇
  Slice-hom (B , f) (C , g) = Σ h ꞉ hom C B , f ＝ h ∘ g

  Slice-homset : {B C : Slice-ob} → is-set (Slice-hom B C)
  Slice-homset {B , e} {C , e'} = γ
   where
    γ : is-set (Σ h ꞉ hom C B , e ＝ (h ∘ e'))
    γ = subsets-of-sets-are-sets (hom C B) (λ h → e ＝ (h ∘ e')) hom-set hom-set

  Slice-u : {B : Slice-ob} → Slice-hom B B
  Slice-u {B , e} = u , unit-l' e

  Slice-_∘_ : {B C D : Slice-ob}
            → Slice-hom C D
            → Slice-hom B C
            → Slice-hom B D
  Slice-_∘_ {B , f} {C , g} {D , e} (h , p) (h' , p') = (h' ∘ h) , γ
   where
    γ : f ＝ ((h' ∘ h) ∘ e)
    γ = f              ＝⟨ p'           ⟩
        (h' ∘ g)       ＝⟨ ap (h' ∘_) p ⟩
        (h' ∘ (h ∘ e)) ＝⟨ assoc e h h' ⟩
        ((h' ∘ h) ∘ e) ∎

  Slice-unit-l : {a b : Slice-ob}
               → (h : Slice-hom a b)
               → Slice-_∘_ Slice-u h ＝ h
  Slice-unit-l {B , f} {C , g} (h , p) = to-Σ-＝ (unit-r h , hom-set _ _)

  Slice-unit-r : {a b : Slice-ob}
               → (h : Slice-hom a b)
               → Slice-_∘_ h Slice-u ＝ h
  Slice-unit-r {B , f} {C , g} (h , p) = to-Σ-＝ (unit-l h , hom-set _ _)

  Slice-assoc : {(B , f) (C , g) (D , k) (E , l) : Slice-ob}
              → (h : Slice-hom (B , f) (C , g))
              → (h' : Slice-hom (C , g) (D , k))
              → (h'' : Slice-hom (D , k) (E , l))
              → Slice-_∘_ h'' (Slice-_∘_ h' h) ＝ Slice-_∘_ (Slice-_∘_ h'' h') h
  Slice-assoc {B , f} {C , g} {D , k} {E , l} (h , p) (h' , p') (h'' , p'')
   = to-Σ-＝ (γ , hom-set _ _)
    where
     γ : (h ∘ h') ∘ h'' ＝ h ∘ (h' ∘ h'')
     γ = assoc h'' h' h ⁻¹

  SlicePC : precategory { 𝓤 ⊔ 𝓥 }
  SlicePC = record
              { ob      = Slice-ob
              ; hom     = Slice-hom
              ; hom-set = Slice-homset
              ; u       = Slice-u
              ; _∘_     = Slice-_∘_
              ; unit-l  = Slice-unit-l
              ; unit-r  = Slice-unit-r
              ; assoc   = Slice-assoc
              }

  {-
  idtoiso-slice : {B C : Slice-ob} → B ＝ C → _≅_ (𝓤 ⊔ 𝓥) SlicePC B C
  idtoiso-slice {a} {.a} refl = Slice-u , Slice-u , (Slice-unit-l Slice-u) , Slice-unit-l Slice-u

  isotoid-slice : {B C : Slice-ob} →  _≅_ (𝓤 ⊔ 𝓥) SlicePC B C → B ＝ C
  isotoid-slice {B , p} {C , p'} (f , g , l , r) = {!!}

  slice-comp1 : {a b : Slice-ob} → (eq : _≅_ (𝓤 ⊔ 𝓥) SlicePC a b) → idtoiso-slice (isotoid-slice eq) ＝ eq
  slice-comp1 {a} {b} eq = {!!}

  slice-comp2 : {a b : Slice-ob} → (e : a ＝ b) → isotoid-slice (idtoiso-slice e) ＝ e
  slice-comp2 = {!!}

  isotoid-slice-has-section : {a b : Slice-ob} → has-section (idtoiso-slice {a} {b})
  isotoid-slice-has-section {a} {b} = isotoid-slice , slice-comp1

  isotoid-slice-is-section : {a b : Slice-ob} → is-section (idtoiso-slice {a} {b})
  isotoid-slice-is-section {a} {b} = isotoid-slice , slice-comp2

  idtoiso-slice-is-equiv : {a b : Slice-ob} → is-equiv (idtoiso-slice { a } { b })
  idtoiso-slice-is-equiv = isotoid-slice-has-section , isotoid-slice-is-section

  SliceCat : category SlicePC
  SliceCat = record { idtoiso-is-equiv = idtoiso-slice , idtoiso-slice-is-equiv }
  -}

\end{code}
