module Structs where

open import Data.List
open import Data.String
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Data.List.Any hiding (map)
open module M {ℓ}{X : Set ℓ} = Membership (PE.setoid X )
import Level

data StructEnd {ℓ} : Set ℓ where
  end : StructEnd

data StructField {ℓ}(s : String)(t : Set ℓ) : Set ℓ where
  _∹_ : (x : String) → {_ : x ≡ s} → t → StructField s t


FieldTypes = λ ℓ → List (String × Set ℓ)

Struct : ∀{ℓ} → FieldTypes ℓ → Set ℓ
Struct [] = StructEnd
Struct {ℓ} ( (n , t) ∷ l) = StructField {ℓ} n t × Struct l

infixr 6 _∶_∷_
data StructLit {ℓ} : FieldTypes ℓ → Set (Level.suc ℓ) where
  [] : StructLit []
  _∶_∷_ : ∀{t : Set ℓ}{ls} → (s : String) → t → StructLit ls → StructLit ((s , t) ∷ ls)


⟨_⟩ : ∀{ℓ}{ls} → StructLit {ℓ} ls → Struct ls
⟨ [] ⟩ = end
⟨ s ∶ x ∷ xs ⟩ = _∹_ s {refl} x , ⟨ xs ⟩

instance
  found-it : ∀{ℓ}{X : Set ℓ}{x : X}{xs : List X}
           → x ∈ (x ∷ xs)
  found-it = here refl
  keep-looking : ∀{ℓ}{X : Set ℓ}{x y : X}{xs : List X}
               → ⦃ t : y ∈ xs ⦄
               → y ∈ (x ∷ xs)
  keep-looking ⦃ t ⦄ = there t


lookup : ∀{ℓ ℓ′}{K : Set ℓ}{V : Set ℓ′}{s}
       → (l : List (K × V)) → s ∈ (map proj₁ l) → V
lookup [] ()
lookup (x ∷ l) (here refl) = proj₂ x
lookup (x ∷ l) (there p)   = lookup l p

update : ∀{ℓ ℓ′}{K : Set ℓ}{V : Set ℓ′}{s}
       → (l : List (K × V)) → s ∈ (map proj₁ l) → V → List (K × V)
update [] () _
update (x ∷ l) (here refl) n = (proj₁ x , n) ∷ l
update (x ∷ l) (there p) n = x ∷ update l p n


field-names = λ{ℓ}(ls : FieldTypes ℓ) → map proj₁ ls

infixl 6 _∙_

_∙_ : ∀{ℓ}{ls : FieldTypes ℓ}
    → Struct ls
    → (s : String) ⦃ prf : s ∈ field-names ls ⦄
    → lookup ls prf
_∙_ {ls = []} _ x ⦃ () ⦄
_∙_ {ls = x ∷ ls} (tg ∹ v , r) ._ ⦃ here refl ⦄ = v
_∙_ {ls = x ∷ ls} (k , r) x₁ ⦃ there prf ⦄ = _∙_ {ls = ls} r x₁ ⦃ prf ⦄


infixl 6 _∙_≔_

module TypeChangingAssignment where

  infixl 6 _∙_≔′_

  _∙_≔′_ : ∀{ℓ}{ls : FieldTypes ℓ}{X : Set ℓ}
        → Struct ls
        → (s : String) ⦃ prf : s ∈ field-names ls ⦄
        → X
        → Struct (update ls prf X)
  _∙_≔′_ {ls = []} s t ⦃ () ⦄ n
  _∙_≔′_ {ls = (q , _) ∷ ls} (_∹_ .q {refl} v , r) ._ ⦃ here refl ⦄ n = _∹_ q {refl} n , r
  _∙_≔′_ {ls = x ∷ ls} (t , r) k  ⦃ there prf ⦄ n = t , (r ∙ k ≔′ n)


  memb-update : ∀{ℓ ℓ′}{K : Set ℓ}{V : Set ℓ′}{ls : List (K × V)}{k}{x : V} → ⦃ prf : k ∈ map proj₁ ls ⦄ → k ∈ map proj₁ (update ls prf x)
  memb-update {ls = []} ⦃ () ⦄
  memb-update {ls = x ∷ ls} {{prf = here refl}} = here refl
  memb-update {ls = x ∷ ls} {{prf = there prf}} = there (memb-update {ls = ls} ⦃ prf ⦄)

  lookup-update : ∀{ℓ ℓ′}{K : Set ℓ}{V : Set ℓ′}{ls : List (K × V)}{k}{x : V}
        → ⦃ prf : k ∈ map proj₁ ls ⦄
        → lookup (update ls prf x) (memb-update ⦃ prf ⦄) ≡ x
  lookup-update {ls = []} ⦃ prf = () ⦄
  lookup-update {ls = x ∷ ls} ⦃ prf = here refl ⦄ = refl
  lookup-update {ls = x ∷ ls} ⦃ prf = there prf ⦄ = lookup-update {ls = ls} ⦃ prf ⦄

  update-lookup : ∀{ℓ ℓ′}{K : Set ℓ}{V : Set ℓ′}{ls : List (K × V)}{k}
                → ⦃ prf : k ∈ map proj₁ ls ⦄
                → update ls prf (lookup ls prf) ≡ ls
  update-lookup {ls = []} ⦃ () ⦄
  update-lookup {ls = x ∷ ls} ⦃ here refl ⦄ = refl
  update-lookup {ls = x ∷ ls} ⦃ there prf ⦄ rewrite update-lookup {ls = ls} ⦃ prf ⦄ = refl


_∙_≔_ : ∀{ℓ}{ls : FieldTypes ℓ}
      → Struct ls
      → (s : String) ⦃ prf : s ∈ field-names ls ⦄
      → lookup ls prf
      → Struct ls
_∙_≔_ {ls = []} s f ⦃ () ⦄ v
_∙_≔_ {ls = x ∷ ls} (_∹_ ._ {refl} _ , r) ._ ⦃ here refl ⦄ v = _∹_ (proj₁ x) {refl} v , r
_∙_≔_ {ls = x ∷ ls} (k , r) f ⦃ there prf ⦄ v = k , r ∙ f ≔ v

spurious-update : ∀{ℓ}{ls : FieldTypes ℓ}{s : Struct ls}{f}
                → ⦃ prf : f ∈ field-names ls ⦄
                → (s ∙ f ≔ (s ∙ f)) ≡ s
spurious-update {ls = []}                         ⦃ () ⦄
spurious-update {ls = _ ∷ _}{_∹_ ._ {refl} _ , _} ⦃ here refl ⦄ = refl
spurious-update {ls = _ ∷ _}{_∹_ ._ {refl} _ , _} ⦃ there prf ⦄ = cong (_,_ _) spurious-update

read-after-update : ∀{ℓ}{ls : FieldTypes ℓ}{s : Struct ls}{f}
                  → ⦃ prf : f ∈ field-names ls ⦄
                  → {v : lookup ls prf}
                  → (s ∙ f ≔ v) ∙ f ≡ v
read-after-update {ls = []}                           ⦃ () ⦄
read-after-update {ls = _ ∷ _}{ _∹_ ._ {refl} _ , _ } ⦃ here refl ⦄ = refl
read-after-update {ls = _ ∷ _}{ _∹_ ._ {refl} _ , _ } ⦃ there prf ⦄ = read-after-update ⦃ prf ⦄

frame-inertia : ∀{ℓ}{ls : FieldTypes ℓ}{s : Struct ls}{f f′}
              → f ≢ f′
              → ⦃ prf : f  ∈ field-names ls ⦄
              → ⦃ prf′ : f′ ∈ field-names ls ⦄
              → {v : lookup ls prf′}
              → (s ∙ f′ ≔ v) ∙ f ≡ (s ∙ f)
frame-inertia {ls = []}                            _ ⦃ () ⦄
frame-inertia {ls = _ ∷ ls}{ _∹_ ._ {refl} _ , _ } _ ⦃ here refl ⦄ ⦃ there prf′ ⦄ = refl
frame-inertia {ls = _ ∷ ls}{ _∹_ ._ {refl} _ , _ } _ ⦃ there prf ⦄ ⦃ here refl  ⦄ = refl
frame-inertia {ls = _ ∷ ls}{ _∹_ ._ {refl} _ , _ } p ⦃ there prf ⦄ ⦃ there prf′ ⦄ = frame-inertia {ls = ls} p
frame-inertia {ls = _ ∷ ls}{ _∹_ ._ {refl} _ , _ } p ⦃ here refl ⦄ ⦃ here refl  ⦄ with p refl
... | ()


append : ∀{ℓ}{ls : FieldTypes ℓ}{ms : FieldTypes ℓ} → Struct ls → Struct ms → Struct (Data.List._++_ ls ms)
append {ls = [] } s₁ s₂ = s₂
append {ls = x ∷ xs} (f , rest) s₂ = f , append rest s₂

drop-append : ∀{ℓ}{ls : FieldTypes ℓ}{ms : FieldTypes ℓ} → Struct (Data.List._++_ ls ms) → Struct ms
drop-append {ls = []} m = m
drop-append {ls = x ∷ xs} (f , rest) = drop-append {ls = xs} rest
