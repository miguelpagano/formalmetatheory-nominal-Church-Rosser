\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
import Atom

module Alpha {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where

open import Term _≟ₐ_ Χ
open import Atom _≟ₐ_
open import Equivariant _≟ₐ_ Χ
open import Permutation _≟ₐ_ Χ
open import ListProperties
open import TermAcc _≟ₐ_ Χ

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum
open import Data.List
open import Data.List.Relation.Unary.Any as Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties  hiding (++⁺ˡ;++⁺ʳ)

infix 3 _∼α_ _≈α_

\end{code}

%<*alpha>
\begin{code}
data _∼α_ : Λ → Λ → Set where
  ∼αv  : {a : Atom} → v a ∼α v a
  ∼α·  : {M M' N N' : Λ} → M ∼α M' → N ∼α N'
       → M · N ∼α M' · N'
  ∼αƛ  : {M N : Λ}{a b : Atom}(xs : List Atom)
       → ((c : Atom) → c ∉ xs → （ a ∙ c ） M ∼α （ b ∙ c ） N)
       → ƛ a M ∼α ƛ b N
\end{code}
%</alpha>

\begin{code}
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

lemma∼αEquiv : EquivariantRel _∼α_
lemma∼αEquiv .{v a}    .{v a}      π (∼αv {a})
  rewrite lemmaπv {a} {π} = ∼αv
lemma∼αEquiv .{M · N}  .{M' · N'}  π (∼α· {M} {M'} {N} {N'} M∼M' N∼N')
  = subst₂ (λ H I → H ∼α I) (sym (lemmaπ· {M} {N} {π})) (sym (lemmaπ· {M'} {N'} {π})) (∼α· (lemma∼αEquiv π M∼M') (lemma∼αEquiv π N∼N'))
lemma∼αEquiv .{ƛ a M}  .{ƛ b N}    π (∼αƛ {M} {N} {a} {b} xs p)
  = subst₂  (λ H I → H ∼α I) (sym (lemmaπƛ {a} {M} {π})) (sym (lemmaπƛ {b} {N} {π}))
            (∼αƛ  {π ∙ M} {π ∙ N} {π ∙ₐ a} {π ∙ₐ b} (xs ++ atoms π)
                  (λ c c∉xs++π → subst₂  (λ H I → H ∼α I)
                                         (  begin≡
                                              π ∙ （ a ∙ c ） M
                                            ≡⟨ lemmaπ∙distributive {a} {c} {M} {π} ⟩
                                              （ π ∙ₐ a ∙ π ∙ₐ c ） (π ∙ M)
                                            ≡⟨ cong (λ H → （ π ∙ₐ a ∙ H ） (π ∙ M)) (lemmaπ∙ₐ≡ {c} {π} (∉-++⁻ʳ xs c∉xs++π)) ⟩
                                              （ π ∙ₐ a ∙ c ） (π ∙ M)
                                            □ )
                                         (  begin≡
                                              π ∙ （ b ∙ c ） N
                                            ≡⟨ lemmaπ∙distributive {b} {c} {N} {π} ⟩
                                              （ π ∙ₐ b ∙ π ∙ₐ c ） (π ∙ N)
                                            ≡⟨ cong (λ H → （ π ∙ₐ b ∙ H ） (π ∙ N)) (lemmaπ∙ₐ≡ {c} {π} (∉-++⁻ʳ xs c∉xs++π)) ⟩
                                              （ π ∙ₐ b ∙ c ） (π ∙ N)
                                            □ )
                                         (lemma∼αEquiv π (p c (∉-++⁻ˡ xs c∉xs++π)))))
--
lemma∼αƛ : {a : Atom}{M N : Λ} → M ∼α N → ƛ a M ∼α ƛ a N
lemma∼αƛ {a} {M} {N} M∼αN = ∼αƛ [] (λ c c∉[] → lemma∼αEquiv [(a , c)] M∼αN)
--
lemma∼αƛ← : {a : Atom}{M N : Λ} → ƛ a M ∼α ƛ a N → M ∼α N
lemma∼αƛ← {a} (∼αƛ xs f) = subst₂  (λ H P → H ∼α P)
                                   lemma（ab）（ab）M≡M
                                   lemma（ab）（ab）M≡M
                                   (lemma∼αEquiv [ ( a , b ) ] (f b b∉xs))
  where
  b = χ' Χ xs
  b∉xs = lemmaχ∉ Χ xs
-- --
ρ : Reflexive _∼α_
ρ {v a}    = ∼αv
ρ {M · N}  = ∼α· ρ ρ
ρ {ƛ a M}  = ∼αƛ [] (λ c c∉[] → lemma∼αEquiv {M} {M} [ (a , c) ] ρ)
--
σ : Symmetric _∼α_
σ ∼αv                = ∼αv
σ (∼α· M∼αM' N∼αN')   = ∼α· (σ M∼αM') (σ N∼αN')
σ (∼αƛ xs p)         = ∼αƛ xs (λ c c∉xs → σ (p c c∉xs))
--
τ : Transitive _∼α_
τ ∼αv ∼αv                            = ∼αv
τ (∼α· M∼αM′ N∼αN′) (∼α· M′∼αM″ N′∼αN″)  = ∼α· (τ M∼αM′ M′∼αM″) (τ N∼αN′ N′∼αN″)
τ (∼αƛ xs p) (∼αƛ xs′ p′)
  = ∼αƛ  (xs ++ xs′)
        (λ c c∉xs++xs′ →
                         τ  (p   c (∉-++⁻ˡ xs c∉xs++xs′))
                            (p′  c (∉-++⁻ʳ xs c∉xs++xs′)))
--
lemma≡→∼ : {M N : Λ} → M ≡ N → M ∼α N
lemma≡→∼ refl = ρ
--
≈-preorder : Preorder _ _ _
≈-preorder =
    record {
      Carrier = Λ;
      _≈_ = _≡_;
      _∼_ = _∼α_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid Λ) ;
        reflexive = λ { {M} {.M} refl → ρ};
        trans = τ } }

import Relation.Binary.Reasoning.Preorder as PreR
open PreR ≈-preorder public
--
lemma∙cancel∼α :  {a b c : Atom}{M : Λ} → b # M → c # M →
                （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ b ） M
lemma∙cancel∼α {a} {b}   {c} {M} b#M c#M with a ≟ₐ b
lemma∙cancel∼α {a} {.a}  {c} {M} a#M c#M
  | yes refl =  begin
                  （ c ∙ a ） （ a ∙ c ） M
                ≈⟨ lemma∙comm  ⟩
                  （ a ∙ c ） （ a ∙ c ） M
                ≈⟨ lemma（ab）（ab）M≡M ⟩
                  M
                ≈⟨ sym lemma（aa）M≡M ⟩
                  （ a ∙ a ） M
                ∎
lemma∙cancel∼α {a} {b}   {c} {M} b#M c#M
  | no a≢b with a ≟ₐ c
lemma∙cancel∼α {a} {b}   {.a} {M} b#M a#M
  | no a≢b | yes refl =   begin
                            （ a ∙ b ） （ a ∙ a ） M
                          ≈⟨ cong (λ x → （ a ∙ b ） x) lemma（aa）M≡M  ⟩
                            （ a ∙ b ） M
                          ∎
lemma∙cancel∼α {a} {b}   {c} {M} b#M c#M
  | no a≢b | no a≢c with b ≟ₐ c
lemma∙cancel∼α {a} {b}   {.b} {M} b#M c#M
  | no a≢b | no a≢c | yes refl =  begin
                                    （ b ∙ b ） （ a ∙ b ） M
                                  ≈⟨ lemma（aa）M≡M ⟩
                                    （ a ∙ b ） M
                                  ∎
lemma∙cancel∼α {a} {b} {c} {v d} (#v d≢b) (#v d≢c) | no a≢b | no a≢c | no b≢c
  =  begin
       （ c ∙ b ） （ a ∙ c ） (v d)
     ≈⟨ refl ⟩
        v (（ c ∙ b ）ₐ （ a ∙ c ）ₐ d)
     ≈⟨ cong v (lemma∙ₐcancel {a} {b} {c} {d} d≢b d≢c) ⟩
        v (（ a ∙ b ）ₐ d)
     ≈⟨ refl ⟩
       （ a ∙ b ） (v d)
     ∎
lemma∙cancel∼α {a} {b} {c} {M · N} (#· b#M b#N) (#· c#M c#N) | no a≢b | no a≢c | no b≢c
  =  ∼α· (lemma∙cancel∼α b#M c#M) (lemma∙cancel∼α b#N c#N)
lemma∙cancel∼α {a} {b} {c} {ƛ d M} b#λdM c#λdM | no a≢b | no a≢c | no b≢c
  with b ≟ₐ d
lemma∙cancel∼α {a} {b} {.b} {ƛ .b M} b#λdM  #ƛ≡       | no a≢b | no _   | no b≢b
  | yes refl = ⊥-elim (b≢b refl)
lemma∙cancel∼α {a} {b} {c} {ƛ .b M} b#λdM   (#ƛ c#M)  | no a≢b | no a≢c | no b≢c
  | yes refl
  rewrite lemma∙ₐ（ab）b≡a {a} {b} | lemma∙ₐc≢a∧c≢b (≢-sym a≢b) b≢c | lemma∙ₐ（ab）b≡a {c} {b}
  = ∼αƛ (a ∷ b ∷ c ∷ Λ-atoms M) (λ  e e∉abc∷atomsM → lemma（ce）（cb）（ac）M∼α（ae）（ab）M e e∉abc∷atomsM)
  where
  lemma（ce）（cb）（ac）M∼α（ae）（ab）M : (e : Atom) → e ∉ a ∷ b ∷ c ∷ Λ-atoms M → （ c ∙ e ） （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ e ） （ a ∙ b ） M
  lemma（ce）（cb）（ac）M∼α（ae）（ab）M  e e∉abc∷atomsM
    = begin
         （ c ∙ e ） （ c ∙ b ） （ a ∙ c ） M
       ≈⟨ lemma∙distributive {c} {e} {c} {b} {（ a ∙ c ） M} ⟩
         （ （ c ∙ e ）ₐ c ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ） （ a ∙ c ） M
       ≈⟨ cong (λ x → （ x ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ） （ a ∙ c ） M) (lemma∙ₐ（ab）a≡b {c} {e}) ⟩
         （ e ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ） （ a ∙ c ） M
       ≈⟨ cong (λ x → （ e ∙ x ） （ c ∙ e ） （ a ∙ c ） M) (lemma∙ₐc≢a∧c≢b b≢c (≢-sym (∉-∷⁼ b∈abc∷atomsM e∉abc∷atomsM))) ⟩
         （ e ∙ b ） （ c ∙ e ） （ a ∙ c ） M
       ∼⟨ lemma∼αEquiv [( e , b)] (lemma∙cancel∼α {a} {e} {c} (lemma∉→# {e} {M} (lemmaΛ-atoms e∉atomsM)) c#M) ⟩
         （ e ∙ b ） （ a ∙ e ）  M
       ≈⟨ sym (cong (λ x → （ e ∙ x ） （ a ∙ e ） M) (lemma∙ₐc≢a∧c≢b (≢-sym a≢b) (≢-sym (∉-∷⁼ b∈abc∷atomsM e∉abc∷atomsM)))) ⟩
         （ e ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ）  M
       ≈⟨ sym (cong (λ x → （ x ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ）  M) (lemma∙ₐ（ab）a≡b {a} {e})) ⟩
         （ （ a ∙ e ）ₐ a ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ）  M
       ≈⟨ sym (lemma∙distributive {a} {e} {a} {b} {M}) ⟩
         （ a ∙ e ） （ a ∙ b ） M
       ∎
   where b∈abc∷atomsM : b ∈ a ∷ b ∷ c ∷ Λ-atoms M
         b∈abc∷atomsM = there (here refl)
         e∉atomsM : e ∉ Λ-atoms M
         e∉atomsM = ∉-++⁻ʳ (a ∷ b ∷ c ∷ []) e∉abc∷atomsM

lemma∙cancel∼α {a} {b} {c} {ƛ d M} b#λdM c#λdM | no a≢b | no a≢c | no b≢c
  | no b≢d with c ≟ₐ d
lemma∙cancel∼α {a} {b} {.b} {ƛ .b M} #ƛ≡ c#λcM      | no a≢b | no a≢d | no _ | no b≢b
  | yes refl = ⊥-elim (b≢b refl)
lemma∙cancel∼α {a} {b} {c} {ƛ .c M} (#ƛ b#M) c#λcM  | no a≢b | no a≢c | no _ | no b≢c
  | yes refl rewrite lemma∙ₐ（ab）b≡a {a} {c} | lemma∙ₐc≢a∧c≢b a≢c a≢b | lemma∙ₐc≢a∧c≢b (≢-sym a≢c) (≢-sym b≢c)
  = ∼αƛ (a ∷ b ∷ c ∷ Λ-atoms M) (λ e e∉abc∷atomsM → lemma（ae）（cb）（ac）M∼α（ce）（ab）M e e∉abc∷atomsM)
  where
  lemma（ae）（cb）（ac）M∼α（ce）（ab）M : (e : Atom) → e ∉ a ∷ b ∷ c ∷ Λ-atoms M → （ a ∙ e ） （ c ∙ b ） （ a ∙ c ） M ∼α （ c ∙ e ） （ a ∙ b ） M
  lemma（ae）（cb）（ac）M∼α（ce）（ab）M e e∉abc∷atomsM
    =  begin
         （ a ∙ e ） （ c ∙ b ） （ a ∙ c ） M
       ≈⟨ cong (λ x → （ a ∙ e ） x) (lemma∙distributive {c} {b} {a} {c} {M}) ⟩
         （ a ∙ e ） （ （ c ∙ b ）ₐ a ∙ （ c ∙ b ）ₐ c ） （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ a ∙ e ） （ x ∙ （ c ∙ b ）ₐ c ） （ c ∙ b ）  M) (lemma∙ₐc≢a∧c≢b a≢c a≢b)  ⟩
         （ a ∙ e ） （ a ∙ （ c ∙ b ）ₐ c ） （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ a ∙ e ） （ a ∙ x ） （ c ∙ b ）  M) (lemma∙ₐ（ab）a≡b {c} {b}) ⟩
         （ a ∙ e ） （ a ∙ b ） （ c ∙ b ）  M
       ≈⟨ lemma∙distributive {a} {e} {a} {b} {（ c ∙ b ）  M}  ⟩
         （ （ a ∙ e ）ₐ a ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ） （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ x ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ） （ c ∙ b ）  M) (lemma∙ₐ（ab）a≡b {a} {e})  ⟩
         （ e ∙ （ a ∙ e ）ₐ b ） （ a ∙ e ） （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ e ∙ x ） （ a ∙ e ） （ c ∙ b ）  M) (lemma∙ₐc≢a∧c≢b (≢-sym a≢b) ((≢-sym (∉-∷⁼ b∈abc∷atomsM e∉abc∷atomsM))))  ⟩
         （ e ∙ b ） （ a ∙ e ） （ c ∙ b ）  M
       ≈⟨ lemma∙distributive {e} {b} {a} {e} {（ c ∙ b ）  M}  ⟩
         （ （ e ∙ b ）ₐ a ∙ （ e ∙ b ）ₐ e ） （ e ∙ b ）  （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ x ∙ （ e ∙ b ）ₐ e ） （ e ∙ b ）  （ c ∙ b ）  M) (lemma∙ₐc≢a∧c≢b (≢-sym ((∉-∷⁼ (here refl) e∉abc∷atomsM))) a≢b)   ⟩
         （ a ∙ （ e ∙ b ）ₐ e ） （ e ∙ b ）  （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ a ∙ x ） （ e ∙ b ）  （ c ∙ b ）  M) (lemma∙ₐ（ab）a≡b {e} {b})  ⟩
         （ a ∙ b ） （ e ∙ b ）  （ c ∙ b ）  M
       ≈⟨ cong (λ x → （ a ∙ b ） x) (lemma∙comm {e} {b} {（ c ∙ b ）  M })  ⟩
         （ a ∙ b ） （ b ∙ e ）  （ c ∙ b ）  M
       ∼⟨ lemma∼αEquiv [(a , b)] (lemma∙cancel∼α {c} {e} {b} {M} (lemma∉→# {e} {M} (lemmaΛ-atoms e∉atomsM)) b#M) ⟩
         （ a ∙ b ） （ c ∙ e ）  M
       ≈⟨ sym (cong (λ x → （ a ∙ x ） （ c ∙ e ）  M) (lemma∙ₐc≢a∧c≢b b≢c ((≢-sym (∉-∷⁼ b∈abc∷atomsM e∉abc∷atomsM))))) ⟩
         （ a ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ）  M
       ≈⟨ sym (cong (λ x → （ x ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ）  M) (lemma∙ₐc≢a∧c≢b a≢c (≢-sym (∉-∷⁼ (here refl) e∉abc∷atomsM)))) ⟩
         （ （ c ∙ e ）ₐ a ∙ （ c ∙ e ）ₐ b ） （ c ∙ e ）  M
       ≈⟨ sym (lemma∙distributive {c} {e} {a} {b} {M}) ⟩
         （ c ∙ e ） （ a ∙ b ） M
       ∎
   where b∈abc∷atomsM : b ∈ a ∷ b ∷ c ∷ Λ-atoms M
         b∈abc∷atomsM = there (here refl)
         e∉atomsM : e ∉ Λ-atoms M
         e∉atomsM = ∉-++⁻ʳ (a ∷ b ∷ c ∷ []) e∉abc∷atomsM

lemma∙cancel∼α {a} {b} {c} {ƛ .b M}  #ƛ≡       c#λdM     | no a≢b | no a≢c | no b≢c | no b≢b
  | no c≢b = ⊥-elim (b≢b refl)
lemma∙cancel∼α {a} {b} {c} {ƛ .c M}  (#ƛ b#M)  #ƛ≡       | no a≢b | no a≢c | no b≢c | no _
  | no c≢c = ⊥-elim (c≢c refl)
lemma∙cancel∼α {a} {b} {c} {ƛ d M}   (#ƛ b#M)  (#ƛ c#M)  | no a≢b | no a≢c | no b≢c | no b≢d
  | no c≢d with a ≟ₐ d
lemma∙cancel∼α {a} {b} {c} {ƛ .a M}   (#ƛ b#M)  (#ƛ c#M)  | no a≢b | no a≢c | no b≢c | no b≢a
  | no c≢a | yes refl rewrite lemma∙ₐ（ab）a≡b {a} {c} | lemma∙ₐ（ab）a≡b {c} {b} | lemma∙ₐ（ab）a≡b {a} {b}
  = lemma∼αƛ (lemma∙cancel∼α b#M c#M)
lemma∙cancel∼α {a} {b} {c} {ƛ d M}   (#ƛ b#M)  (#ƛ c#M)  | no a≢b | no a≢c | no b≢c | no b≢d
  | no c≢d | no a≢d rewrite lemma∙ₐc≢a∧c≢b (≢-sym a≢d) (≢-sym c≢d) | lemma∙ₐc≢a∧c≢b (≢-sym c≢d) (≢-sym b≢d) | lemma∙ₐc≢a∧c≢b (≢-sym a≢d) (≢-sym b≢d)
  = lemma∼αƛ (lemma∙cancel∼α b#M c#M)
--
lemma∙cancel∼α' : {a b c : Atom}{M : Λ} → b # ƛ a M → c # M → （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ b ） M
lemma∙cancel∼α' {a} {.a} {c} {M}       #ƛ≡     c#M
  = begin
      （ c ∙ a ） （ a ∙ c ） M
    ≈⟨ lemma∙comm {c} {a} {（ a ∙ c ） M} ⟩
      （ a ∙ c ） （ a ∙ c ） M
    ≈⟨ lemma（ab）（ab）M≡M {a} {c} {M} ⟩
       M
    ≈⟨ sym (lemma（aa）M≡M {a} {M}) ⟩
      （ a ∙ a ） M
    ∎
lemma∙cancel∼α' {a} {b} {c} {M}       (#ƛ b#M)     c#M
  = lemma∙cancel∼α {a} {b} {c} {M} b#M  c#M
--
lemma∙cancel∼α'' : {a b c : Atom}{M : Λ} → b # ƛ a M → c # ƛ a M → （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ b ） M
lemma∙cancel∼α'' {a} {b} {.a} {M} b#ƛaM #ƛ≡ rewrite lemma（aa）M≡M {a} {M} = ρ
lemma∙cancel∼α'' b#ƛaM (#ƛ c#M) = lemma∙cancel∼α' b#ƛaM c#M
--
lemma∙cancel∼α‴ : {a b c : Atom}{M : Λ} → b # M → c # ƛ a M → （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ b ） M
lemma∙cancel∼α‴ {a} {b} {.a}  {M} b#M #ƛ≡ rewrite lemma（aa）M≡M {a} {M} = ρ
lemma∙cancel∼α‴ {a} {b} {c}   {M}  b#M (#ƛ c#N)  = lemma∙cancel∼α b#M c#N
--
lemma∙ : {a b c : Atom}{M : Λ} → b # ƛ a M → c ∉ₜ M → （ c ∙ b ） （ a ∙ c ） M ∼α （ a ∙ b ） M
lemma∙ {a} {b} {c} {M}       b#ƛaM     c∉M
  = lemma∙cancel∼α' {a} {b} {c} {M} b#ƛaM (lemma∉→# c∉M)
--
lemma∼α* : {a : Atom}{M N : Λ} → M ∼α N → a * M → a * N
lemma∼α* {a}                  ∼αv               a*M           = a*M
lemma∼α* {a}                  (∼α· M∼αM' N∼αN')   (*·l a*M)     = *·l (lemma∼α* M∼αM' a*M)
lemma∼α* {a}                  (∼α· M∼αM' N∼αN')   (*·r a*N)     = *·r (lemma∼α* N∼αN' a*N)
lemma∼α* {a} {ƛ b M} {ƛ c N}  (∼αƛ xs f)        (*ƛ a*M b≢a)
  with
  χ' Χ (a ∷ b ∷ c ∷ [] ++ xs ++ Λ-atoms N) |
  ∉-++⁻ˡ {v = χ' Χ (a ∷ b ∷ c ∷ [] ++ xs ++ Λ-atoms N)} xs
    (∉-++⁻ʳ (a ∷ b ∷ c ∷ []) (lemmaχ∉ Χ (a ∷ b ∷ c ∷ [] ++ xs ++ Λ-atoms N))) |
  (lemmaχ∉ Χ (a ∷ b ∷ c ∷ [] ++ xs ++ Λ-atoms N))
... | d | d∉xs | d∉abcxsN
  with lemma*swap← (lemma∼α* (f d d∉xs) (lemma*swap→ a≢d (≢-sym b≢a) a*M))
  where
  a≢d : a ≢ d
  a≢d a≡d = d∉abcxsN (here (sym a≡d))
lemma∼α* {a} {ƛ b M} {ƛ c N} (∼αƛ xs f) (*ƛ a*M b≢a)
  | d | d∉xs | d∉abcxsN | inj₁ (a≢c , _ , a*N)     = *ƛ a*N (≢-sym a≢c)
lemma∼α* {a} {ƛ b M} {ƛ c N} (∼αƛ xs f) (*ƛ a*M b≢a)
  | d | d∉xs | d∉abcxsN | inj₂ (inj₁ (a≡c , d*N))  = ⊥-elim ((¬d*N) d*N)
  where
  d∉N : d ∉ₜ N
  d∉N = lemmaΛ-atoms (∉-++⁻ʳ xs (∉-++⁻ʳ (a ∷ b ∷ c ∷ []) d∉abcxsN))
  ¬d*N : ¬ (d * N)
  ¬d*N d*N = (lemma∉→¬∈ d∉N) (lemma-free→∈ d*N)
lemma∼α* {a} {ƛ b M} {ƛ c N} (∼αƛ xs f) (*ƛ a*M b≢a)
  | d | d∉xs | d∉abcxsN | inj₂ (inj₂ (_ , a≡d , c*N))  = ⊥-elim (a≢d a≡d)
  where
  a≢d : a ≢ d
  a≢d a≡d = d∉abcxsN (here (sym a≡d))
--
lemma∼α# : {a : Atom}{M N : Λ} → M ∼α N → a # M → a # N
lemma∼α# {a} {M} {N} M∼N a#M with a #? N
... | yes a#N = a#N
... | no ¬a#N = ⊥-elim (lemma-free→¬# (lemma∼α* (σ M∼N) (lemma¬#→free ¬a#N)) a#M)
-- Chi Alpha Lemma
χ∼α : (M N : Λ)(xs : List Atom) → M ∼α N → χ xs M ≡ χ xs N
χ∼α M N xs M∼αN = lemmaχaux⊆ Χ (xs ++ fv M) (xs ++ fv N) lemma⊆ lemma⊇
  where
  lemma⊆ : (xs ++ fv M) ⊆ (xs ++ fv N)
  lemma⊆ {a} a∈xs++fvM with ∈-++⁻ xs a∈xs++fvM
  ... | inj₁ a∈xs   = xs⊆xs++ys xs (fv N) a∈xs
  ... | inj₂ a∈fvM  = xs⊆ys++xs (fv N) xs (lemmafvfree← a N (lemma∼α* M∼αN (lemmafvfree→ a M (a∈fvM))))
  lemma⊇ : (xs ++ fv N) ⊆ (xs ++ fv M)
  lemma⊇ {a} a∈xs++fvN with ∈-++⁻ xs a∈xs++fvN
  ... | inj₁ a∈xs   = xs⊆xs++ys xs (fv M) a∈xs
  ... | inj₂ a∈fvN  = xs⊆ys++xs (fv M) xs (lemmafvfree← a M (lemma∼α* (σ M∼αN) (lemmafvfree→ a N (a∈fvN))))
-- A more classical alpha definition
data _≈α_ : Λ → Λ → Set where
  ≈αv  : {a : Atom}
       → v a ≈α v a
  ≈α·  : {M M' N N' : Λ} → M ≈α M' → N ≈α N'
       → M · N ≈α M' · N'
  ≈αƛ  : {M N : Λ}{a b c : Atom}
       → c # ƛ a M → c # ƛ b N
       → （ a ∙ c ） M ≈α （ b ∙ c ） N
       → ƛ a M ≈α ƛ b N
--
lemma∼α∃#→∀ : {a b c : Atom}{M N : Λ} →
         c # ƛ a M → c # ƛ b N → （ a ∙ c ） M ∼α  （ b ∙ c ） N →
         ∃ (λ xs → ((d : Atom) →  d ∉ xs → （ a ∙ d ） M ∼α  （ b ∙ d ） N))
lemma∼α∃#→∀ {a} {b} {c} {M} {N} c#ƛaM c#ƛbN （ac）M∼α（bc）N
  = Λ-atoms M ++ Λ-atoms N ,
    (λ  d d∉atomsM++atomsN →
        (lemmaEqRel _∼α_ lemma∼αEquiv) [(d , c)]
                                         (  begin
                                              （ d ∙ c ） （ a ∙ d ） M
                                            ∼⟨ lemma∙ c#ƛaM (lemmaΛ-atoms (∉-++⁻ˡ (Λ-atoms M) d∉atomsM++atomsN)) ⟩
                                              （ a ∙ c ） M
                                            ∼⟨ （ac）M∼α（bc）N ⟩
                                              （ b ∙ c ） N
                                            ∼⟨ σ (lemma∙ c#ƛbN (lemmaΛ-atoms ((∉-++⁻ʳ (Λ-atoms M) d∉atomsM++atomsN)) )) ⟩
                                              （ d ∙ c ） （ b ∙ d ） N
                                            ∎ ))
--
lemma∼α∀→∃# : {a b : Atom}{M N : Λ}{xs : List Atom} →
         ((c : Atom) →  c ∉ xs → （ a ∙ c ） M ∼α  （ b ∙ c ） N) →
         ∃ (λ c → c # ƛ a M ∧ c # ƛ b N ∧ （ a ∙ c ） M ∼α （ b ∙ c ） N)
lemma∼α∀→∃# {a} {b} {M} {N} {xs} f
  with χ' Χ (xs ++ Λ-atoms (ƛ a M) ++ Λ-atoms (ƛ b N))  | lemmaχ∉ Χ (xs ++ Λ-atoms (ƛ a M) ++ Λ-atoms (ƛ b N))
... | c | c∉xs++atomsƛaM++atomsƛbN
  =  c ,
     (lemma∉→#
       (lemmaΛ-atoms
          (∉-++⁻ˡ (Λ-atoms (ƛ a M)) (∉-++⁻ʳ xs c∉xs++atomsƛaM++atomsƛbN)))) ,
     (lemma∉→#
       (lemmaΛ-atoms
         (∉-++⁻ʳ (Λ-atoms (ƛ a M)) (∉-++⁻ʳ xs c∉xs++atomsƛaM++atomsƛbN)))) ,
     (f c (∉-++⁻ˡ xs c∉xs++atomsƛaM++atomsƛbN))

-- Alpha definitions equivalence; Study if this proof can be done with an induction principle without Accesible predicate !
lemma∼α→≈αAcc : {M N : Λ} → ΛAcc M → M ∼α N → M ≈α N
lemma∼α→≈αAcc _                 ∼αv                = ≈αv
lemma∼α→≈αAcc (acc· accM accN)  (∼α· M∼αM' N∼αN')  = ≈α· (lemma∼α→≈αAcc accM M∼αM') (lemma∼α→≈αAcc accN N∼αN')
lemma∼α→≈αAcc (accƛ facc)       (∼αƛ _ f) with lemma∼α∀→∃# f
... | c , c#λaM , c#λbN , （ac）M∼α（bc）N = ≈αƛ {c = c} c#λaM c#λbN (lemma∼α→≈αAcc (facc c) （ac）M∼α（bc）N)

lemma∼α→≈α : {M N : Λ} → M ∼α N → M ≈α N
lemma∼α→≈α {M} M∼N = lemma∼α→≈αAcc {M} (accesibleTerms M) M∼N
--
lemma≈α→∼α : {M N : Λ} → M ≈α N → M ∼α N
lemma≈α→∼α ≈αv              = ∼αv
lemma≈α→∼α (≈α· M≈αM' N≈αN')  = ∼α· (lemma≈α→∼α M≈αM') (lemma≈α→∼α N≈αN')
lemma≈α→∼α (≈αƛ c#ƛaM c#ƛbN （ac）M∼α（bc）N)
  with lemma∼α∃#→∀ c#ƛaM c#ƛbN (lemma≈α→∼α （ac）M∼α（bc）N)
... | xs , prf = ∼αƛ xs prf
--
lemma∼αλ : {a b : Atom}{M : Λ} → b # M → ƛ a M ∼α ƛ b (（ a ∙ b ） M)
lemma∼αλ {a} {b} {M} b#M
  = ∼αƛ (Λ-atoms M) (λ c c∉atomsM → σ (lemma∙cancel∼α (lemma∉→# (lemmaΛ-atoms c∉atomsM)) b#M))
--
lemma∼αλ' : {a b : Atom}{M : Λ} → b # ƛ a M → ƛ a M ∼α ƛ b (（ a ∙ b ） M)
lemma∼αλ' {a} {.a} {M} #ƛ≡ rewrite lemma（aa）M≡M {a} {M} = ρ
lemma∼αλ' (#ƛ b#M) = lemma∼αλ b#M
--
lemma~αswap : {a b : Atom}{M N : Λ} → ƛ a M ∼α ƛ b N → （ b ∙ a ） M ∼α N
lemma~αswap {a} {b} {M} {N} ƛaM~ƛbN
  = lemma∼αƛ← {b} (τ ( subst (λ N → ƛ b N ∼α ƛ a M) lemma∙comm (σ (lemma∼αλ' (lemma∼α# (σ ƛaM~ƛbN) #ƛ≡)))) ƛaM~ƛbN)
--
lemma∼λχ : {a : Atom}{vs : List Atom}{M : Λ} → ƛ a M ∼α ƛ (χ vs (ƛ a M)) (（ a ∙ (χ vs (ƛ a M)) ） M)
lemma∼λχ {a} {vs} {M}
  = lemma∼αλ' (χ# vs (ƛ a M))
--
lemma#∼α : {a b : Atom}{M : Λ} → a # M → b # M → M ∼α （ a ∙ b ） M
lemma#∼α {a} {b} {v d}     (#v d≢a)      (#v d≢b)
  rewrite lemma∙ₐc≢a∧c≢b d≢a d≢b     = ρ
lemma#∼α {a} {b} {M · N}   (#· a#M a#N)  (#· b#M b#N)
  = ∼α· (lemma#∼α a#M b#M) (lemma#∼α a#N b#N)
lemma#∼α {a} {b} {ƛ c M}   a#ƛcM         b#ƛcM
  with a ≟ₐ c
lemma#∼α {a} {.a} {ƛ .a M} a#ƛaM         #ƛ≡
  | yes refl
  rewrite lemma（aa）M≡M {a} {ƛ a M}  = ρ
lemma#∼α {a} {b} {ƛ .a M}  a#ƛaM         (#ƛ b#M)
  | yes refl
  rewrite lemma∙ₐ（ab）a≡b {a} {b}    = lemma∼αλ b#M
lemma#∼α {a} {b} {ƛ c M}   a#ƛcM  b#ƛcM
  | no  a≢c with b ≟ₐ c
lemma#∼α {.b} {b} {ƛ .b M} #ƛ≡ #ƛ≡
  | no b≢b | yes refl = ⊥-elim (b≢b refl)
lemma#∼α {a} {b} {ƛ .b M} (#ƛ a#M) #ƛ≡
  | no a≢b | yes refl
  rewrite lemma∙ₐ（ab）b≡a {a} {b}
  |       lemma∙comm {a} {b} {M}     = lemma∼αλ a#M
lemma#∼α {.b} {b} {ƛ .b M} #ƛ≡ (#ƛ b#M)
  | no b≢b | yes refl = ⊥-elim (b≢b refl)
lemma#∼α {a} {b} {ƛ .b M} (#ƛ a#M) (#ƛ b#M)
  | no a≢b | yes refl
  rewrite lemma∙ₐ（ab）b≡a {a} {b}
  |       lemma∙comm {a} {b} {M}     = lemma∼αλ a#M
lemma#∼α {a} {b} {ƛ c M}   a#ƛcM  b#ƛcM
  | no  a≢c | no b≢c
  rewrite lemma∙ₐc≢a∧c≢b (≢-sym a≢c) (≢-sym b≢c)
  = lemma∼αƛ (lemma#∼α (lemma#λ a≢c a#ƛcM) (lemma#λ b≢c b#ƛcM))
\end{code}

Alpha Compatibility

%<*alphaCompatible>
\begin{code}
αCompatiblePred : {l : Level} → (Λ → Set l) → Set l
αCompatiblePred P = {M N : Λ} → M ∼α N → P M → P N
\end{code}
%</alphaCompatible>

Strong Compatibility

%<*strongAlphaCompatible>
\begin{code}
strong∼αCompatible  : {l : Level} {A : Set l}
                    → (Λ → A) → Λ → Set l
strong∼αCompatible f M = ∀ N → M ∼α N → f M ≡ f N
\end{code}
%</strongAlphaCompatible>
