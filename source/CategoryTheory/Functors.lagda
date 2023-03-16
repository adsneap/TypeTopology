\begin{code}

{-# OPTIONS --allow-unsolved-metas #-}

open import MLTT.Spartan renaming (_∘_ to _∘'_)

open import CategoryTheory.Type
open import CategoryTheory.Properties
open import UF.Subsingletons

module CategoryTheory.Functors where

record Functor (A : precategory {𝓤} {𝓥})
               (B : precategory {𝓦} {𝓣}) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where

 open precategory
 private
  _∘A_ = _∘_ A
  _∘B_ = _∘_ B

 field
  _⟶    : ob A → ob B
  _⇒ : {a b : ob A} → hom A a b → hom B (a ⟶) (b ⟶)
  Fid  : {a : ob A} → _⇒ { a } (u A) ＝ u B
  _∘F_ : {a b c : ob A} {f : hom A a b} {g : hom A b c} → _⇒ (g ∘A f) ＝ _⇒ g ∘B _⇒ f

record NaturalTransformation
  {A : precategory {𝓤} {𝓥}}
  {B : precategory {𝓦} {𝓣}}
  (F G : Functor A B) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 where
 open Functor
 open precategory
 private
  _⟶F = _⟶ F
  _⟶G = _⟶ G
  _⇒F = _⇒ F
  _⇒G = _⇒ G
  _∘B_ = _∘_ B
 field
  γ : (a : ob A) → hom B (a ⟶F) (a ⟶G)
  naturality-axiom : {a b : ob A}
                   → (f : hom A a b)
                   → (f ⇒G) ∘B (γ a) ＝ γ b ∘B (f ⇒F)

 NaturalTransformationIsSet : is-set (NaturalTransformation F G)
 NaturalTransformationIsSet = {!!}

-- Functor Precategory

module FunctorPrecategory
 (A : precategory { 𝓤 } { 𝓥 })
 (B : precategory { 𝓦 } { 𝓣 })
  where

 open precategory
 open Functor
 open NaturalTransformation
 
 private
  _∘A_ = _∘_ A
  _∘B_ = _∘_ B

 ufPC : {F : Functor A B} → NaturalTransformation F F
 ufPC {F} = let _⇒F = _⇒ F
            in
            record { γ = λ a → u B
                   ; naturality-axiom = λ f → (f ⇒F) ∘B (u B) ＝⟨ unit-r B (f ⇒F) ⟩
                                              (f ⇒F)          ＝⟨ unit-l B (f ⇒F) ⁻¹ ⟩
                                              u B ∘B (f ⇒F)   ∎ }
 _∘fPC_ : {F G H : Functor A B}
        → (ψ : NaturalTransformation G H)
        → (δ : NaturalTransformation F G)
        → NaturalTransformation F H
 _∘fPC_ {F} {G} {H} ψ δ = let _⇒F = _⇒ F
                              _⇒G = _⇒ G
                              _⇒H = _⇒ H
                          in
                          record { γ = λ a → (γ ψ a) ∘B γ δ a
                                 ; naturality-axiom = λ {a} {b} f → (f ⇒H) ∘B (γ ψ a ∘B γ δ a)   ＝⟨ assoc B (γ δ a) (γ ψ a) (f ⇒H) ⟩
                                                                    ((f ⇒H) ∘B γ ψ a) ∘B γ δ a   ＝⟨ ap (_∘B γ δ a) (naturality-axiom ψ f) ⟩
                                                                    (γ ψ b ∘B (f ⇒G)) ∘B γ δ a   ＝⟨ assoc B (γ δ a) (f ⇒G) (γ ψ b) ⁻¹ ⟩
                                                                    γ ψ b ∘B ((f ⇒G) ∘B γ δ a)   ＝⟨ ap (γ ψ b ∘B_) (naturality-axiom δ f) ⟩
                                                                    γ ψ b ∘B (γ δ b ∘B (f ⇒F))   ＝⟨ assoc B (f ⇒F) (γ δ b) (γ ψ b) ⟩
                                                                    (γ ψ b ∘B γ δ b) ∘B (f ⇒F) ∎ }
                                              
 functorPC : precategory
 functorPC = record
               { ob = Functor A B
               ; hom = NaturalTransformation
               ; hom-set = λ {F} {G} {γ} → NaturalTransformationIsSet γ
               ; u =  ufPC 
               ; _∘_ = _∘fPC_
               ; unit-l = λ {F} {G} f → (ufPC ∘fPC f) ＝⟨ {!!} ⟩
                                        {!!}          ＝⟨ {!!} ⟩
                                        {!!}          ＝⟨ {!!} ⟩
                                        f             ∎
               ; unit-r = {!!}
               ; assoc = {!!}
               }
         
\end{code}

Fibration

\begin{code}



module Fibration
  (𝓐 : precategory { 𝓤 } { 𝓥 })
  (𝓑 : precategory { 𝓦 } { 𝓣 })
  (F : Functor 𝓐 𝓑)
 where

 open precategory
 open Functor
 open NaturalTransformation
 private
  _⟶F = _⟶ F
  _⇒F = _⇒ F
  hom𝓐 = hom 𝓐
  ob𝓐 = ob 𝓐
  hom𝓑 = hom 𝓑
  _∘𝓐_ = _∘_ 𝓐
  id𝓐 = u 𝓐
  id𝓑 = u 𝓑

 g-cartesian : (D E : ob𝓐) → hom𝓐 D E → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 g-cartesian D E f =
  (D' : ob𝓐) → (f' : hom𝓐 D' E) → ∃! g ꞉ hom𝓐 D' D , (g ⇒F ＝ {!id𝓑 !})
                                                     × (f' ＝ f ∘𝓐 g)

 fibration : (B : ob 𝓑) → 𝓤 ⊔ 𝓦 ̇
 fibration B = Σ A ꞉ ob 𝓐 , B ＝ A ⟶F

\end{code}
