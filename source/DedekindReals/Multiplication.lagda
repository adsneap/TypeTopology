Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import Notation.Order
open import UF.PropTrunc 
open import UF.Subsingletons 
open import UF.FunExt 
open import UF.Powerset 

open import Rationals.Rationals
open import Rationals.Order

module DedekindReals.Multiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.MinMax fe
open import DedekindReals.Reals pe pt fe
open PropositionalTruncation pt


\end{code}

Multiplication is defined as in the HoTT Book. It reminds of interval multiplication of rational numbers.

Inhabitedness: by inhabitedness of x and y, we find values
on both sides of each. Then using the property that rationals have no
least element, then using the relevant min/max calculation we
trivially find a p which inhabits each cut of the product.

Roundedness: roundedness in the left to right direction follows
directly from density of rationals, and transitivity of rationals
order. In the right to left, transivity alone completes the proof.

_*_ : ℝ → ℝ → ℝ
x * y = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R , is-disjoint , {!!}
 where
  L R : 𝓟 ℚ
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) , ∃-is-prop
  R q = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q) , ∃-is-prop

  x-values : ∥ (Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , x < b) ∥
  x-values = binary-choice (inhabited-from-real-L x) (inhabited-from-real-R x)

  y-values : ∥ (Σ c ꞉ ℚ , c < y) × (Σ d ꞉ ℚ , y < d) ∥
  y-values = binary-choice (inhabited-from-real-L y) (inhabited-from-real-R y)

  xy-values : ∥ ((Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , x < b)) × ((Σ c ꞉ ℚ , c < y) × (Σ d ꞉ ℚ , y < d)) ∥
  xy-values = binary-choice x-values y-values

  inhabited-L : inhabited-left L
  inhabited-L = ∥∥-functor I xy-values
   where
    I : ((Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , x < b)) × ((Σ c ꞉ ℚ , c < y) × (Σ d ꞉ ℚ , y < d))
      → Σ p ꞉ ℚ , p ∈ L
    I (((a , a<x) , (b , x<b)) , ((c , c<y) , (d , y<d))) = II (ℚ-no-least-element (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)))
     where
      II : (Σ p ꞉ ℚ , p <  min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
         → Σ p ꞉ ℚ , p ∈ L
      II (p , p<m) = p , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , p<m) ∣

  inhabited-R : inhabited-right R
  inhabited-R = ∥∥-functor I xy-values
   where
    I : ((Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , x < b)) × ((Σ c ꞉ ℚ , c < y) × (Σ d ꞉ ℚ , y < d))
      → Σ q ꞉ ℚ , q ∈ R
    I (((a , a<x) , (b , x<b)) , ((c , c<y) , (d , y<d))) = II (ℚ-no-max-element (max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)))
     where
      II : (Σ q ꞉ ℚ , max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q)
         → Σ q ꞉ ℚ , q ∈ R
      II (q , m<q) =  q , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , m<q) ∣

  rounded-L : rounded-left L
  rounded-L p = ltr , rtl
   where
    ltr : p ∈ L → ∃ p' ꞉ ℚ , p < p' × p' ∈ L
    ltr = ∥∥-functor I
     where
      I : (Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
        → Σ p' ꞉ ℚ , p < p' × p' ∈ L
      I ((a , b , c , d) , a<x , x<b , c<y , y<d , p<m) = II (ℚ-dense fe p (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<m)
       where
        II : (Σ p' ꞉ ℚ , p < p' × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) → Σ p' ꞉ ℚ , p < p' × p' ∈ L
        II (p' , p<p' , p'<m) = p' , (p<p' , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , p'<m) ∣)
    rtl : ∃ p' ꞉ ℚ , (p < p') × (p' ∈ L) → p ∈ L
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℚ , (p < p') × (p' ∈ L) → p ∈ L
      I (p' , p<p' , p'<xy) = ∥∥-functor II p'<xy
       where
        II : (Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
           → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
        II ((a , b , c , d) , a<x , x<b , c<y , y<d , p'<m)= (a , b , c , d) , (a<x , x<b , c<y , y<d , ℚ<-trans p p' (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<p' p'<m)

  rounded-R : rounded-right R
  rounded-R q = ltr , rtl 
   where
    ltr : q ∈ R → ∃ q' ꞉ ℚ , (q' < q) × (q' ∈ R)
    ltr = ∥∥-functor I 
     where
      I : (Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q)
        → Σ q' ꞉ ℚ , (q' < q) × (q' ∈ R)
      I ((a , b , c , d) , a<x , x<b , c<y , y<d , m<q) = II (ℚ-dense fe (max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) q m<q)
       where
        II : (Σ q' ꞉ ℚ , (max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q') × (q' < q)) → Σ q' ꞉ ℚ , (q' < q) × (q' ∈ R)
        II (q' , m<q' , q'<q) = q' , q'<q , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , m<q') ∣
    rtl : ∃ q' ꞉ ℚ , (q' < q) × (q' ∈ R) → q ∈ R
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℚ , (q' < q) × (q' ∈ R) → q ∈ R
      I (q' , q'<q , xy<q') = ∥∥-functor II xy<q'
       where
        II : Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q'
           → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q
        II ((a , b , c , d) , a<x , x<b , c<y , y<d , m<q') = (a , b , c , d) , (a<x , x<b , c<y , y<d , ℚ<-trans (max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) q' q m<q' q'<q)

  is-disjoint : disjoint L R
  is-disjoint p q (p<xy , xy<q) = {!!}
 
\end{code}
