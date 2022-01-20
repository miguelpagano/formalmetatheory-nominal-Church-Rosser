open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Diamond (Atom : Set) (_≟ₐ_ : Decidable {A = Atom} _≡_) where

open import Atom Atom _≟ₐ_
open import Term Atom _≟ₐ_ hiding (fv)
open import Alpha Atom _≟ₐ_ hiding (step-≡)
open import TermAcc Atom _≟ₐ_
open import ListProperties
open import TermInduction Atom _≟ₐ_
open import TermRecursion Atom _≟ₐ_
open import Substitution Atom _≟ₐ_
open import FreeVariables Atom _≟ₐ_
open import Parallel Atom _≟ₐ_
open import Relation Λ hiding (_++_) renaming (_⊆_ to _⊆R_)

open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Relation.Unary.Any as Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_];trans)

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

_* : Λ → Λ
(v x)          *  = v x
((v x)    · N) *  = v x       · (N *)
((M · M′) · N) *  = (M · M′)* · (N *)
((ƛ x M)  · N) *  = (M *) [ x ≔ N * ]
(ƛ x M)        *  = ƛ x (M *)

lemma* : {M N : Λ} → M ⇉ N → N ⇉ M *
lemma* {v .x}           (⇉v x)                = ⇉v x
lemma* {ƛ x M}          λxM⇉N
  with lemma⇉ƛrule λxM⇉N
... | N′ , M⇉N′ , ƛxM⇉ƛxN′ , N~ƛxN′           = lemma⇉αleft N~ƛxN′ (lemma⇉ƛpres (lemma* M⇉N′))
lemma* {v x      · M}   (⇉· x⇉N M⇉N′)         = ⇉· (lemma* x⇉N) (lemma* M⇉N′)
lemma* {(M · M′) · M″}  (⇉· MM′⇉N M″⇉N′)      = ⇉· (lemma* MM′⇉N) (lemma* M″⇉N′)
lemma* {ƛ x  M   · M′}  (⇉· .{ƛ x M} {N} .{M′} {N′} ƛxM⇉N M′⇉N′)
 with lemma⇉ƛrule ƛxM⇉N
... | N″ , M⇉N″ , _ , N~ƛxN″
  = lemma⇉αleft (∼α· N~ƛxN″ ρ) (⇉β x x (lemma⇉ƛpres (lemma* M⇉N″)) (lemma* M′⇉N′) ρ)
lemma* {ƛ .x M   · M′}  (⇉β .{M} {N} .{M′} {N′} {P} x y ƛxM⇉ƛyN M′⇉N′ N[y≔N′]~P)
 with lemma⇉ƛrule ƛxM⇉ƛyN
... | N″ , M⇉N″ , _ , ƛyN~ƛxN″
  = lemma⇉αleft P~N″[x≔N′] (lemma⇉Subst x N″ (lemma* M⇉N″) (lemma* M′⇉N′))
  where
  P~N″[x≔N′] : P ∼α N″ [ x ≔ N′ ]
  P~N″[x≔N′] =  begin
                   P
                ∼⟨ σ N[y≔N′]~P ⟩
                   N  [ y ≔ N′ ]
                ∼⟨ σ (lemmaSwapSubstVar' x y N′ N (lemma∼α# (σ ƛyN~ƛxN″) #ƛ≡)) ⟩
                   (（ x ∙ y ） N) [ x ≔ N′ ]
                ≈⟨ lemmaSubst1 N′ x (lemma~αswap ƛyN~ƛxN″)  ⟩
                   N″ [ x ≔ N′ ]
                ∎
--
diam⇉2 :  {M N P : Λ} → M ⇉ N → M ⇉ P
         → ∃ (λ Q → N ⇉ Q × P ⇉ Q)
diam⇉2 {M} M⇉N M⇉P = (M *) , lemma* M⇉N , lemma* M⇉P
