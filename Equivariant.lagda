\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])

module Equivariant (Atom : Set) (_≟ₐ_ : Decidable {A = Atom} _≡_) where
open import AtomAbs Atom _≟ₐ_
open import Term Atom _≟ₐ_
open import Permutation Atom _≟ₐ_

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

EquivariantPred : (Λ → Set) → Set
EquivariantPred P = {M : Λ}(π : Π) → P M → P (π ∙ M)
--
EquivariantRel : (Λ → Λ → Set) → Set
EquivariantRel R = {M N : Λ}(π : Π) → R M N → R (π ∙ M) (π ∙ N)
--
EquivariantRel← : (Λ → Λ → Set) → Set
EquivariantRel← R = {M N : Λ}(π : Π) → R (π ∙ M) (π ∙ N) → R M N
--
lemmaEqRel : (R : Λ → Λ → Set) → EquivariantRel R → EquivariantRel← R
lemmaEqRel R EqR {M} {N} π RπMπN
  with EqR (π ⁻¹) RπMπN
... | Rπ⁻¹πMπ⁻¹πN rewrite lemmaπ⁻¹∘π≡id {π} {M} | lemmaπ⁻¹∘π≡id {π} {N}
  = Rπ⁻¹πMπ⁻¹πN
--
EquivariantRela : (Atom → Λ → Set) → Set
EquivariantRela R = {a : Atom}{M : Λ}(π : Π) → R a M → R (π ∙ₐ a) (π ∙ M)
--
lemma#Equiv : EquivariantRela _#_
lemma#Equiv {a} .{v b}    π (#v {b} b≢a)
  rewrite lemmaπv {b} {π}
  = #v (lemmaππ∙ₐinj {b} {a} {π} b≢a)
lemma#Equiv {a} .{M · N}  π (#· {M} {N} a#M a#N)
  rewrite lemmaπ· {M} {N} {π}
  = #· (lemma#Equiv π a#M) (lemma#Equiv π a#N)
lemma#Equiv {a} .{ƛ a M}  π (#ƛ≡ {M})
  rewrite lemmaπƛ {a} {M} {π}
  = #ƛ≡
lemma#Equiv {a} {ƛ b M}   π (#ƛ a#M)
  rewrite lemmaπƛ {b} {M} {π}
  = #ƛ (lemma#Equiv π a#M)
--
lemma∉swap : {a b c : Atom}{M : Λ} → a ∉ₜ M → （ b ∙ c ）ₐ a ∉ₜ （ b ∙ c  ） M
lemma∉swap {a} {b} {c}   {m} a∉m with b ≟ₐ c
lemma∉swap {a} {b} {.b}  {m} a∉m
  | yes refl rewrite lemma（aa）M≡M {b} {m} | lemma（aa）b≡b {b} {a}
  = a∉m
lemma∉swap {a} {b} {c} {v d} (∉v d≢a) | no b≢c        = ∉v (lemma∙ₐinj d≢a)
lemma∉swap {a} {b} {c} {m · n} (∉· a∉m a∉n) | no b≢c  = ∉· (lemma∉swap a∉m) (lemma∉swap a∉n)
lemma∉swap {a} {b} {c} {ƛ d m} (∉ƛ d≢a a∉m) | no b≢c  = ∉ƛ (lemma∙ₐinj d≢a) (lemma∉swap a∉m)
\end{code}
