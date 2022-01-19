\begin{code}
module ListProperties where

open import Function
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Nat
open import Data.Product renaming (Σ to Σₓ;map to mapₓ)
open import Data.Bool hiding (_∨_;_≟_)
open import Data.List hiding (any)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.Membership.Propositional as Any
open import Data.List.Relation.Unary.Any as AnyDef using ()
open import Data.List.Relation.Unary.Any.Properties hiding (concat⁺)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open Any renaming (_∈_ to _∈'_;_∉_ to _∉'_)
open AnyDef.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties  hiding (++⁺ˡ;++⁺ʳ)
import Function.Equality as FE
open import Function.Inverse hiding (sym;_∘_;map;id)
open Function.Inverse.Inverse

-- Auxiliary functions and properties
_-_ : ∀ {A : Set} {_≟ₐ_ : Decidable {A = A} (_≡_)} → List A → A → List A
_-_ {A} {_≟ₐ_} xs x = filter (λ y → ¬? (x ≟ₐ y)) xs

--
lemma∈ : {Γ : List ℕ}{x y : ℕ} → y ∈' x ∷ Γ → x ≢ y → y ∈' Γ
lemma∈ {Γ} {x} .{x}  (here refl) x≢y = ⊥-elim (x≢y refl)
lemma∈ {Γ} {x} {y}   (there y∈Γ) x≢y = y∈Γ
--

++-lub : ∀ {A : Set} {ws ys xs : List A} → ws ⊆ xs → ys ⊆ xs → ws ++ ys ⊆ xs
++-lub {ws = ws} sub sub' {x} inc with ++⁻ ws inc
... | inj₁ x₁ = sub x₁
... | inj₂ y = sub' y


lemmaΓ⊆Γ++Γ : {Γ : List ℕ} → Γ ++ Γ ⊆ Γ
lemmaΓ⊆Γ++Γ {Γ} = ++-lub {ys = Γ} (λ z → z) λ z → z

--
lemmaΓ⊆Γ++Δ : {Γ Δ : List ℕ} → Γ ⊆ Γ ++ Δ
lemmaΓ⊆Γ++Δ {Γ} {Δ} = xs⊆xs++ys Γ Δ
--
lemmaΓ,x,y⊆Γ,y,x : {x y : ℕ}{Γ : List ℕ} → y ∷ x ∷ Γ ⊆ x ∷ y ∷ Γ
lemmaΓ,x,y⊆Γ,y,x (here refl)          = there (here refl)
lemmaΓ,x,y⊆Γ,y,x (there (here refl))  = here refl
lemmaΓ,x,y⊆Γ,y,x (there (there z∈Γ))  = there (there z∈Γ)
--
lemmaΓ++Δ,x⊆Γ,x++Δ : {Γ Δ : List ℕ}{x : ℕ} → Γ ++ x ∷ Δ ⊆ x ∷ Γ ++ Δ
lemmaΓ++Δ,x⊆Γ,x++Δ {Γ} {Δ} {x} {y} rewrite sym (++-identityʳ Δ)
  = concat⁺ {xss = Γ ∷ [ x ] ∷ Δ ∷ []} {[ x ] ∷ Γ ∷ Δ ∷ []} hip
  where
    xss = Γ ∷ ([ x ]) ∷ Δ ∷ []
    yss = ((x ∷ []) ∷ Γ ∷ Δ ∷ [])
    hip : xss ⊆ yss
    hip (here px) = there (here px)
    hip (there (here px)) = here px
    hip (there (there x₂)) = there (there x₂)

∉-++⁻ : {A : Set} {v : A} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ xs) × (v ∉ ys)
∉-++⁻ xs v∉xs++ys =
      (λ v∈xs → ⊥-elim (v∉xs++ys (++⁺ˡ v∈xs))) ,
      λ v∈ys → ⊥-elim (v∉xs++ys (++⁺ʳ xs v∈ys))

∉-++⁻ˡ : {A : Set} {v : A} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ xs)
∉-++⁻ˡ xs v∉xs++ys = proj₁ (∉-++⁻ xs v∉xs++ys)

∉-++⁻ʳ : {A : Set} {v : A} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ ys)
∉-++⁻ʳ xs v∉xs++ys = proj₂ (∉-++⁻ xs v∉xs++ys)

∉-∷⁼ : {A : Set} {a d : A} {xs : List A} → a ∈ xs → d ∉ xs → d ≢ a
∉-∷⁼ a∈xs d∉xs d≡a rewrite d≡a = d∉xs a∈xs

∉-∷⁺ : {A : Set} {a d : A} {xs : List A} → d ≢ a → d ∉ xs → d ∉ (a ∷ xs)
∉-∷⁺ d≢a d∉xs (here px) = d≢a px
∉-∷⁺ d≢a d∉xs (there d∈a∷xs) = d∉xs d∈a∷xs

∉-∷⁼ᵗ : {A : Set} {a d : A}{xs : List A} → d ∉ (a ∷ xs) → d ∉ xs
∉-∷⁼ᵗ d∉∷ d∈xs = d∉∷ (there d∈xs)

\end{code}

First element to satisfy some property.

\begin{code}
data First {A : Set}
         (P : A → Set) : List A → Set where
  here  : ∀ {x xs} (px  : P x)                        → First P (x ∷ xs)
  there : ∀ {x xs} (¬px : ¬ (P x))(pxs : First P xs)  → First P (x ∷ xs)
\end{code}
