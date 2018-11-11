module Control.Recursion.Scheme where

open import Prelude.Functor
open import Agda.Primitive
open import Data.Product
open import Size
open import Prelude.Function
open import Data.Functor.Regular
open import Data.Sum
open import Data.Unit
open import Control.Comonad
open import Prelude.Function

private
  variable
    l : Level
    i : Size

data Project {l} (i : Size) (A : Size → Set l) (F : Set l → Set l) : Set l where
  prj : {j : Size< i} → F (A j) → Project i A F

record Recursive {l} (A : Size → Set l) : Set (lsuc l) where
  field
    Base : Set l -> Set l
    {{baseFun}} : Functor Base
    project : {i : Size} → A i → Project i A Base

  cata : {B : Set l} → (Base B → B) → A i → B
  cata h x with project x
  cata h x | prj y = h $ fmap {{baseFun}} (cata h) y

  para : {B : Set l} → ({j : Size} → Base (A j × B) → B) → A i → B
  para h x with project x
  para h x | prj y = h $ fmap {{baseFun}} (λ z → z , para h z) y
open Recursive {{...}} public

instance
  regularRec : {F : Regular {l}} → Recursive {l} (λ i → μ i F)
  regularRec {F = F} =
    record { Base = ⟦ F ⟧'
           ; project = λ{ (fix x) → prj (mkR x) } }

variable
  A : Set l
  B : Set l
  T : Size → Set l
  F : Set l → Set l
  W : Set l → Set l

hylo : {{_ : Functor F}} {A : Size → Set l}
     → (F B → B) → ({i : Size} → A i → Project i A F) → A i → B
hylo f g x with g x
hylo f g x | prj y = f $ fmap (hylo f g) y

fold = cata
refold = hylo

gcata : {{r : Recursive T}} {{_ : Comonad W}}
      → ((∀{B} → Base {{r}} (W B) → W (Base {{r}} B)))
      → (Base {{r}} (W A) → A)
      → T i
      → A
gcata {T = T'} k g = g ∘ extract ∘ aux
  where
    aux : T' i → _
    aux x with project x
    aux x | prj y = k (fmap (duplicate ∘ fmap g ∘ aux) y)

gfold = gcata

distZygo : {{_ : Functor F}} → (F B → B) → F (B × A) → B × F A
distZygo g m = g (fmap proj₁ m) , fmap proj₂ m

zygo : {{r : Recursive T}} {A B : Set l}
     → (Base {{r}} B → B) → (Base {{r}} (B × A) → A)
     → T i → A
zygo f g x = gcata (distZygo f) g x
