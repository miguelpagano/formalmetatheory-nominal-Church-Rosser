\begin{code}
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module NoCapture (Atom : Set) (_≟ₐ_ : Decidable {A = Atom} _≡_) where

open import AtomAbs Atom _≟ₐ_
open import Equivariant Atom _≟ₐ_
open import Term Atom _≟ₐ_ hiding (fv)
open import Alpha Atom _≟ₐ_ hiding (step-≡)
open import TermAcc Atom _≟ₐ_
open import ListProperties
open import Permutation Atom _≟ₐ_
open import TermInduction Atom _≟ₐ_
open import TermRecursion Atom _≟ₐ_
open import Substitution Atom _≟ₐ_
open import FreeVariables Atom _≟ₐ_
open import Relation Λ hiding (_++_;trans) renaming (_⊆_ to _⊆R_)

open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Relation.Unary.Any as Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
\end{code}
No capture lemma

\begin{code}
PC→ : Atom → Atom → Λ → Λ → Set
PC→ a b N M = a ∈ fv (M [ b ≔ N ]) → a ∈ fv M -ₐ b ++ fv N
\end{code}

\begin{code}
PC→αComp : ∀ a b N → αCompatiblePred (PC→ a b N)
PC→αComp a b N {M} {P} M∼P PC→M a∈fvP[b≔N]
  rewrite lemmaSubst1 {P} {M} N b (σ M∼P) | lemma∼αfv {P} {M} (σ M∼P)
  = PC→M a∈fvP[b≔N]
\end{code}

\begin{code}
lemmaNoCapture : ∀ {a b N M} → PC→ a b N M
lemmaNoCapture {a} {b} {N} {M}
  = TermαPrimInd (PC→ a b N) (PC→αComp a b N) lemmav lemma· (a ∷ b ∷ fv N , lemmaƛ) M
  where
  lemmav : (c : Atom) → PC→ a b N (v c)
  lemmav c  a∈fva[b≔N] with (v c) [ b ≔ N ] | lemmahvar {b} {c} {N}
  lemmav c  a∈fvN
    | .N      | inj₁ (b≡a , refl)
    = ∈-++⁺ʳ ([ c ] -ₐ b) a∈fvN
  lemmav c (there ()) | .(v c) | inj₂ (b≢c , refl)
  lemmav .a (here refl) | .(v a) | inj₂ (b≢a , refl)
    = ∈-++⁺ˡ  (∈-filter⁺ (λ x → ¬? (b ≟ₐ x) ) (here refl) b≢a)
  lemma· : (M P : Λ) → PC→ a b N M → PC→ a b N P → PC→ a b N (M · P)
  lemma· M P PC→M PC→P a∈fvMP[b≔N] with ∈-++⁻ (fv (M [ b ≔ N ])) a∈fvMP[b≔N]
  lemma· M P PC→M PC→P _ | inj₁ a∈fvM[b≔N] with ∈-++⁻ (fv M -ₐ b) (PC→M a∈fvM[b≔N])
  ... | inj₂ a∈N = ∈-++⁺ʳ (fv (M · P) -ₐ b) a∈N
  ... | inj₁ a∈fvM-b with ∈-filter⁻ (λ y → ¬? (b ≟ₐ y)) {xs = fv M} a∈fvM-b
  ...   | a∈fvM , px
    = ∈-++⁺ˡ (∈-filter⁺ ((λ y → ¬? (b ≟ₐ y))) (∈-++⁺ˡ a∈fvM) px )
  lemma· M P PC→M PC→P _ | inj₂ a∈fvP[b≔N] with ∈-++⁻ (fv P -ₐ b) (PC→P a∈fvP[b≔N])
  ... | inj₂ a∈N = ∈-++⁺ʳ (fv (M · P) -ₐ b) a∈N
  ... | inj₁ a∈fvP-b with ∈-filter⁻ (λ y → ¬? (b ≟ₐ y)) {xs = fv P} a∈fvP-b
  ...   | a∈fvP , px
    =  ∈-++⁺ˡ {xs = fv (M · P) -ₐ b} (∈-filter⁺ (λ y → ¬? (b ≟ₐ y)) {xs = fv (M · P)} (∈-++⁺ʳ (fv M) a∈fvP) px)
  lemmaƛ : (M : Λ) (c : Atom) → c ∉ a ∷ b ∷ fv N → PC→ a b N M → PC→ a b N (ƛ c M)
  lemmaƛ M c c∉abfvN PC→M a∈fvƛcM[b≔N] with ∈-++⁻ (fv M -ₐ b) (PC→M (lemma∈fvƛbM→a∈fvM {a} {c} {M [ b ≔ N ]} a≢c a∈fvƛcM[b≔N]'))
    where
    a≢c : a ≢ c
    a≢c = λ a≡c → ⊥-elim (c∉abfvN (here (sym a≡c)))
    c∉b∷fvN : c ∉ b ∷ fv N
    c∉b∷fvN = λ c∈b∷fvN → ⊥-elim (c∉abfvN (there c∈b∷fvN))
    a∈fvƛcM[b≔N]' : a ∈ fv (ƛ c (M [ b ≔ N ]))
    a∈fvƛcM[b≔N]' rewrite sym (lemma∼αfv (lemmaƛ∼[] {b} {c} {N} M c∉b∷fvN)) = a∈fvƛcM[b≔N]
  ... | inj₂ a∈N = ∈-++⁺ʳ (fv (ƛ c M) -ₐ b) a∈N
  ... | inj₁ a∈fvM-b = ∈-++⁺ˡ a∈fvƛcM-b
    where
    a∈fvM,a≢b = ∈-filter⁻ ((λ y → ¬? (b ≟ₐ y))) a∈fvM-b
    a∈fvM : a ∈ fv M
    a∈fvM = proj₁ a∈fvM,a≢b
    a≢c : a ≢ c
    a≢c = λ a≡c → ⊥-elim (c∉abfvN (here (sym a≡c)))
    a∈fvƛcM-b : a ∈ fv (ƛ c M) -ₐ b
    a∈fvƛcM-b = ∈-filter⁺ (¬? ∘ (_≟ₐ_ b)) (lemma∈fvM→a∈fvƛbM {a} {c} {M} a≢c a∈fvM) (proj₂ a∈fvM,a≢b )
\end{code}

\begin{code}
PC← : Atom → Atom → Λ → Λ → Set
PC← a b N M = b ∈ fv M → a ∈ fv N → a ∈ fv (M [ b ≔ N ])
\end{code}
