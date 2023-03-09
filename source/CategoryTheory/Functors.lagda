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

-- idtoiso-preserved : {a b : ob A} → F a ＝ F b → _≅_ 𝓦 B (F a) (F b)
-- idtoiso-preserved e = {!!} , {!!}

record NaturalTransformation {A : precategory {𝓤} {𝓥}} {B : precategory {𝓦} {𝓣}} (F G : Functor A B) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where
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


{- λ {F} → record { γ = λ a → Functor._⇒ F (u A)
                                     ; naturality-axiom = λ f → (Functor._⇒ F f ∘B Functor._⇒ F (u A)) ＝⟨ Functor._∘F_ F ⁻¹ ⟩
                                                          Functor._⇒ F (f ∘A (u A)) ＝⟨ ap (Functor._⇒ F) (unit-r A f) ⟩
                                                          Functor._⇒ F f                        ＝⟨ ap (Functor._⇒ F) (unit-l A f ⁻¹) ⟩
                                                          Functor._⇒ F (u A ∘A f)   ＝⟨ Functor._∘F_ F ⟩
                                                          (Functor._⇒ F (u A) ∘B Functor._⇒ F f) ∎ } -}
