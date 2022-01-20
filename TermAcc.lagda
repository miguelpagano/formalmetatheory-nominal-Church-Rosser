\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])

module TermAcc (Atom : Set) (_≟ₐ_ : Decidable {A = Atom} _≡_) where

open import Term Atom _≟ₐ_
open import Atom Atom _≟ₐ_

-- Induction over terms size, perserved under swapping
open import Data.Nat
open import NaturalProperties
open import Induction.WellFounded
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality
--
data ΛAcc : Λ → Set where
  accv   : {a : Atom}  → ΛAcc (v a)
  acc·   : {M N : Λ}   → ΛAcc M → ΛAcc N → ΛAcc (M · N)
  accƛ   : {a : Atom}{M : Λ} → ((b : Atom) → ΛAcc (（ a ∙ b ） M)) → ΛAcc (ƛ a M)
--
accTerms : ∀ M m → Acc _<′_ m → ∣ M ∣ ≡ m → ΛAcc M
accTerms (v x)   .1              _      refl  = accv
accTerms (M · N) .(∣ M ∣ + ∣ N ∣)  (acc f) refl
  = acc·  (accTerms M ∣ M ∣ (f ∣ M ∣ ((lemman>0→m+1≤m+n {∣ M ∣} {∣ N ∣} (sizePositive {N})))) refl)
          (accTerms N ∣ N ∣ (f ∣ N ∣ ((lemmam>0→n+1≤m+n {∣ M ∣} {∣ N ∣} (sizePositive {M})))) refl)
accTerms (ƛ a M) .(1 + ∣ M ∣)     (acc f) refl
  = accƛ (λ b → accTerms (（ a ∙ b ） M) ∣ M ∣ (f ∣ M ∣ ≤′-refl)  (lemma∙∣∣ {M}))
--
accesibleTerms : ∀ M → ΛAcc M
accesibleTerms M = accTerms M ∣ M ∣ (<′-wellFounded ∣ M ∣) refl
--
data ΛAccSizeƛ : Λ → Set where
  accSv   : {a : Atom}  → ΛAccSizeƛ (v a)
  accS·   : {M N : Λ}   → ΛAccSizeƛ M → ΛAccSizeƛ N → ΛAccSizeƛ (M · N)
  accSƛ   : {a : Atom}{M : Λ} → ((N : Λ) → ∣ N ∣ <′ 1 + ∣ M ∣ → ΛAccSizeƛ N) → ΛAccSizeƛ (ƛ a M)
--
accTermSizes : ∀ M m → Acc _<′_ m → ∣ M ∣ ≡ m → ΛAccSizeƛ M
accTermSizes (v x)   .1              _      refl  = accSv
accTermSizes (M · N) .(∣ M ∣ + ∣ N ∣)  (acc f) refl
  = accS·  (accTermSizes M ∣ M ∣ (f ∣ M ∣ ((lemman>0→m+1≤m+n {∣ M ∣} {∣ N ∣} (sizePositive {N})))) refl)
           (accTermSizes N ∣ N ∣ (f ∣ N ∣ ((lemmam>0→n+1≤m+n {∣ M ∣} {∣ N ∣} (sizePositive {M})))) refl)
accTermSizes (ƛ a M) .(1 + ∣ M ∣)     (acc f) refl
  = accSƛ  (λ N ∣N∣<1+∣M∣ → accTermSizes N ∣ N ∣ (f ∣ N ∣ ∣N∣<1+∣M∣)  refl)
--
getFirstacc· : {M N : Λ} → ΛAccSizeƛ (M · N) → ΛAccSizeƛ M
getFirstacc· (accS· accM accN) = accM
--
getSecondacc· : {M N : Λ} → ΛAccSizeƛ (M · N) → ΛAccSizeƛ N
getSecondacc· (accS· accM accN) = accN
--
accesibleTermsSizesƛ : ∀ M → ΛAccSizeƛ M
accesibleTermsSizesƛ M = accTermSizes M ∣ M ∣ (<′-wellFounded ∣ M ∣) refl
\end{code}
