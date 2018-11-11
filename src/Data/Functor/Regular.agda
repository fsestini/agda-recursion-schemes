module Data.Functor.Regular where

open import Size
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Prelude.Functor
open import Prelude.Function

private
  variable l : Level

data Regular {l} : Set (lsuc l) where
  |I| : Regular {l}
  |K| : Set l -> Regular {l}
  _|+|_ : Regular {l} -> Regular {l} -> Regular {l}
  _|×|_ : Regular {l} -> Regular {l} -> Regular {l}

⟦_⟧ : Regular {l} -> Set l -> Set l
⟦ |I| ⟧ = λ A → A
⟦ |K| B ⟧ = λ A → B
⟦ F |+| G ⟧ = λ A → ⟦ F ⟧ A ⊎ ⟦ G ⟧ A
⟦ F |×| G ⟧ = λ A → ⟦ F ⟧ A × ⟦ G ⟧ A

data μ {l} (i : Size) (F : Regular {l}) : Set l where
  fix : {j : Size< i} → ⟦ F ⟧ (μ j F) → μ i F

record ⟦_⟧' {l} (F : Regular {l}) (A : Set l) : Set l where
  no-eta-equality
  constructor mkR
  field
    unFunctor : ⟦ F ⟧ A
open ⟦_⟧'

instance
  regularFunctor : {F : Regular {l}} → Functor ⟦ F ⟧'
  regularFunctor {F = |I|} =
    record { fmap = λ { f (mkR x) → mkR (f x) }}
  regularFunctor {F = |K| x} =
    record { fmap = λ { f (mkR x) → mkR x }}
  regularFunctor {F = F |+| G} =
    let fmpF = fmap {{regularFunctor {F = F}}} ; fmpG = fmap {{regularFunctor {F = G}}}
    in record { fmap = λ { f (mkR (inj₁ x)) →
                               mkR (inj₁ (unFunctor $ fmpF f (mkR x)))
                         ; f (mkR (inj₂ y)) →
                               mkR (inj₂ (unFunctor $ fmpG f (mkR y))) } }
  regularFunctor {F = F |×| G} =
    let fmpF = fmap {{regularFunctor {F = F}}} ; fmpG = fmap {{regularFunctor {F = G}}}
    in record { fmap = λ { f (mkR (fst , snd)) →
         mkR ((unFunctor $ fmpF f (mkR fst))
                   ,(unFunctor $ fmpG f (mkR snd))) }}
