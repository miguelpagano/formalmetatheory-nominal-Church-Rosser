\begin{code}
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Atom
module Parallel {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where

open import Atom _≟ₐ_
open import Equivariant _≟ₐ_ Χ
open import Term _≟ₐ_ Χ hiding (fv)
open import Alpha _≟ₐ_ Χ hiding (step-≡)
open import TermAcc _≟ₐ_ Χ
open import ListProperties
open import Permutation _≟ₐ_ Χ
open import TermInduction _≟ₐ_ Χ
open import TermRecursion _≟ₐ_ Χ
open import Substitution _≟ₐ_ Χ
open import FreeVariables _≟ₐ_ Χ
open import Relation Λ hiding (_++_;trans) renaming (_⊆_ to _⊆R_)

open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Relation.Unary.Any as Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
\end{code}

\begin{code}
infixl 3 _⇉_
\end{code}

Parallel reduction.

%<*parallel>
\begin{code}
data _⇉_ : Rel where
  ⇉v :  (x : Atom)
        → v x ⇉ v x
  ⇉ƛ :  {M M' : Λ}{x y : Atom}(xs : List Atom)
        → ((z : Atom) → z ∉ xs → （ x ∙ z ） M ⇉ （ y ∙ z ） M')
        → ƛ x M ⇉ ƛ y M'
  ⇉· :  {M M' N N' : Λ}
        → M ⇉ M' → N ⇉ N'
        → M · N ⇉ M' · N'
  ⇉β :  {M M' N N' P : Λ}(x y : Atom)
        → ƛ x M ⇉ ƛ y M'
        → N ⇉ N'
        → M' [ y ≔ N' ] ∼α P
        → ƛ x M · N ⇉ P
\end{code}
%</parallel>

\begin{code}
lemma⇉ƛ : {x : Atom}{M N : Λ} → ƛ x M ⇉ N
           → ∃ (λ y → ∃ (λ P → ∃ (λ ys → N ≡ ƛ y P × ((z : Atom) → z ∉ ys → （ x ∙ z ） M ⇉ （ y ∙ z ） P))))
lemma⇉ƛ {x} {M} {ƛ y P} (⇉ƛ ys fys) = y , P , ys , refl , fys
\end{code}


Parallel diamond property.

\begin{code}
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

lemma⇉Equiv : EquivariantRel (_⇉_)
lemma⇉Equiv π (⇉v x)
  = subst (λ H → H ⇉ H) (sym (lemmaπv {x} {π})) (⇉v (π ∙ₐ x))
lemma⇉Equiv π (⇉ƛ {M} {M'} {x} {y} xs fxs)
  = subst₂  (λ H I → H ⇉ I) (sym (lemmaπƛ {x} {M} {π})) (sym (lemmaπƛ {y} {M'} {π}))
            (⇉ƛ (xs ++ atoms π)
                (λ z z∉xs++π →  subst₂  (λ H I → H ⇉ I)
                                        (  begin≡
                                             π ∙ （ x ∙ z ） M
                                           ≡⟨ lemmaπ∙distributive {x} {z} {M} {π} ⟩
                                             （ π ∙ₐ x ∙ π ∙ₐ z ） (π ∙ M)
                                           ≡⟨ cong (λ H → （ π ∙ₐ x ∙ H ） (π ∙ M)) (lemmaπ∙ₐ≡ {z} {π} (∉-++⁻ʳ xs z∉xs++π)) ⟩
                                             （ π ∙ₐ x ∙ z ） (π ∙ M)
                                           □ )
                                        (  begin≡
                                             π ∙ （ y ∙ z ） M'
                                           ≡⟨ lemmaπ∙distributive {y} {z} {M'} {π} ⟩
                                             （ π ∙ₐ y ∙ π ∙ₐ z ） (π ∙ M')
                                           ≡⟨ cong (λ H → （ π ∙ₐ y ∙ H ） (π ∙ M')) (lemmaπ∙ₐ≡ {z} {π} (∉-++⁻ʳ xs z∉xs++π)) ⟩
                                             （ π ∙ₐ y ∙ z ） (π ∙ M')
                                           □ )
                                        (lemma⇉Equiv π (fxs z (∉-++⁻ˡ xs z∉xs++π)))))
lemma⇉Equiv π (⇉· {M} {M'} {N} {N'} M⇉M' N⇉N')
  = subst₂  (λ H I → H ⇉ I) (sym (lemmaπ· {M} {N} {π})) (sym (lemmaπ· {M'} {N'} {π}))
            (⇉· (lemma⇉Equiv π M⇉M') (lemma⇉Equiv π N⇉N'))
lemma⇉Equiv π (⇉β {M} {M'} {N} {N'} {P} x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼P)
  = subst  (λ H → H ⇉ π ∙ P)
           (sym (trans (lemmaπ· {ƛ x M} {N} {π}) (cong (λ H → H · (π ∙ N)) (lemmaπƛ {x} {M} {π}))))
           (⇉β  {π ∙ M} {π ∙ M'} {π ∙ N} {π ∙ N'} {π ∙ P} (π ∙ₐ x) (π ∙ₐ y)
                (subst₂ (λ H I → H ⇉ I) (lemmaπƛ {x} {M} {π}) (lemmaπƛ {y} {M'} {π}) (lemma⇉Equiv π ƛxM⇉ƛyM'))
                (lemma⇉Equiv π N⇉N')
                (begin
                   (π ∙ M') [ π ∙ₐ y ≔ π ∙ N' ]
                 ∼⟨  σ (lemmaπ[] {M'} {N'} {y} {π})  ⟩
                   π ∙ (M' [ y ≔ N' ])
                 ∼⟨ lemma∼αEquiv π M'[y≔N']∼P ⟩
                   π ∙ P
                 ∎))

lemma⇉ƛpres : {x : Atom}{M N : Λ} → M ⇉ N → ƛ x M ⇉ ƛ x N
lemma⇉ƛpres {x} M⇉N =  ⇉ƛ [] ( λ y _ → lemma⇉Equiv [ (x , y) ] M⇉N)

lemma⇉αright : {M N P : Λ} → M ⇉ N → N ∼α P → M ⇉ P
lemma⇉αright (⇉v a)          ∼αv
  = ⇉v a
lemma⇉αright (⇉· M⇉M' N⇉N')  (∼α· M'∼P N'∼P')
  = ⇉· (lemma⇉αright M⇉M' M'∼P) (lemma⇉αright N⇉N' N'∼P')
lemma⇉αright (⇉ƛ xs fxs)     (∼αƛ ys fys)
  = ⇉ƛ  (xs ++ ys)
        (λ z z∉xs++ys → lemma⇉αright (fxs z (∉-++⁻ˡ xs z∉xs++ys)) (fys z (∉-++⁻ʳ xs z∉xs++ys)))
lemma⇉αright (⇉β x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼N) N∼P
  = ⇉β x y ƛxM⇉ƛyM' N⇉N' (τ M'[y≔N']∼N N∼P)

lemma⇉αleft : {M N P : Λ} → M ∼α N → N ⇉ P → M ⇉ P
lemma⇉αleft ∼αv          (⇉v a)
  = ⇉v a
lemma⇉αleft (∼αƛ xs fxs) (⇉ƛ ys fys)
  = ⇉ƛ (xs ++ ys) (λ z z∉xs++ys → lemma⇉αleft (fxs z (∉-++⁻ˡ xs z∉xs++ys)) (fys z (∉-++⁻ʳ xs z∉xs++ys)))
lemma⇉αleft (∼α· M∼M' N∼N') (⇉· M'⇉P N'⇉P')
  = ⇉· (lemma⇉αleft M∼M' M'⇉P) (lemma⇉αleft N∼N' N'⇉P')
lemma⇉αleft (∼α· {ƛ z M} {ƛ .x N} {M'} {N'} ƛzM∼ƛxN M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P)
  = ⇉β z y (lemma⇉αleft ƛzM∼ƛxN ƛxN⇉ƛyP') (lemma⇉αleft M'∼N' N'⇉P'') P'[x≔P'']∼P
lemma⇉αleft (∼α· {v _}   {ƛ .x N} {M'} {N'} () M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P)
lemma⇉αleft (∼α· {_ · _} {ƛ .x N} {M'} {N'} () M'∼N') (⇉β x y ƛxN⇉ƛyP' N'⇉P'' P'[x≔P'']∼P)

P⇉# : Atom → Λ → Set
P⇉# x M = {N : Λ} → x # M → M ⇉ N → x # N

αCompP⇉# : (x : Atom) → αCompatiblePred (P⇉# x)
αCompP⇉# x {M} {P} M~P PM x#P P⇉N = PM (lemma∼α# (σ M~P) x#P) (lemma⇉αleft M~P P⇉N)

lemma⇉# : {M : Λ}{x : Atom} → P⇉# x M
lemma⇉# {M} {x} = TermαIndPerm
                      (P⇉# x)
                      (αCompP⇉# x)
                      lemmav
                      lemma·
                      ([ x ] , lemmaƛ)
                      M
   where
   lemmav : (a : Atom) → P⇉# x (v a)
   lemmav a x#a (⇉v .a)
     = x#a
   lemma· : (M P : Λ) → P⇉# x M → P⇉# x P → P⇉# x (M · P)
   lemma· M P PM PP (#· x#M x#P) (⇉· M⇉N' P⇉N'')
     = #· (PM x#M M⇉N') (PP x#P P⇉N'')
   lemma· (ƛ .y M) P PƛyM PP (#· x#ƛyM x#P) (⇉β y z ƛyM⇉ƛzN' P⇉N'' N'[z:=N'']∼N)
     = lemma∼α# N'[z:=N'']∼N (lemma#Subst (PƛyM x#ƛyM ƛyM⇉ƛzN') (PP x#P P⇉N''))
   lemmaƛ : (M : Λ) (b : Atom) → b ∉ [ x ] → (∀ π → P⇉# x (π ∙ M)) → P⇉# x (ƛ b M)
   lemmaƛ M .x  x∉[x] PπM {ƛ y N} #ƛ≡       (⇉ƛ xs fxs)
     = ⊥-elim (x∉[x] (here refl))
   lemmaƛ M b   b∉[x] PπM {ƛ y N} (#ƛ x#M)  (⇉ƛ xs fxs)
     = corollarylemma*swap→ x≢z (PπM [ ( b , z ) ] x#（bz）M (fxs z z∉xs))
     where
     z = χ' Χ (x ∷ fv N ++ xs)
     z∉x∷fvN++xs = lemmaχ∉ Χ (x ∷ fv N ++ xs)
     z∉xs : z ∉ xs
     z∉xs = ∉-++⁻ʳ (x ∷ fv N) z∉x∷fvN++xs
     x≢z : x ≢ z
     x≢z = ≢-sym (∉-∷⁼ (here refl) z∉x∷fvN++xs)
     x≢b : x ≢ b
     x≢b x≡b = ⊥-elim (b∉[x] (here (sym x≡b)))
     x#（bz）M : x # （ b ∙ z ） M
     x#（bz）M = lemma#swap≢ x≢b x≢z x#M

lemma⇉ƛrule : {M M' : Λ}{x : Atom}
        → ƛ x M ⇉ M'
        → Σ Λ (λ M″ → M ⇉ M″ × ƛ x M ⇉ ƛ x M″ × M' ∼α ƛ x M″)
lemma⇉ƛrule {M} {ƛ y M'} {x} (⇉ƛ xs fxs)
  =  （ y ∙ x ） M'                            ,
     M⇉（yx）M'                                ,
     lemma⇉αright (⇉ƛ xs fxs) ƛyM'∼ƛx（yx）M'  ,
     ƛyM'∼ƛx（yx）M'
  where
  x#ƛyM' : x # ƛ y M'
  x#ƛyM' = lemma⇉# #ƛ≡ (⇉ƛ xs fxs)
  ƛyM'∼ƛx（yx）M' : ƛ y M' ∼α ƛ x (（ y ∙ x ） M')
  ƛyM'∼ƛx（yx）M' = lemma∼αλ' x#ƛyM'
  z : Atom
  z = χ' Χ (xs ++ fv (ƛ y M'))
  z∉xs : z ∉ xs
  z∉xs = ∉-++⁻ˡ xs (lemmaχ∉ Χ (xs ++ fv (ƛ y M')))
  z#ƛyM' : z # ƛ y M'
  z#ƛyM' = lemma∉fv→# (∉-++⁻ʳ xs (lemmaχ∉ Χ (xs ++ fv (ƛ y M'))))
  M⇉（yx）M' : M ⇉ （ y ∙ x ） M'
  M⇉（yx）M' = lemma⇉αright
                 (subst (λ H → H ⇉ （ x ∙ z ） （ y ∙ z ） M') lemma（ab）（ab）M≡M (lemma⇉Equiv [ (x , z) ] (fxs z z∉xs)))
                 (  begin
                      （ x ∙ z ） （ y ∙ z ） M'
                    ≈⟨ lemma∙comm ⟩
                      （ z ∙ x ） （ y ∙ z ） M'
                    ∼⟨ lemma∙cancel∼α'' x#ƛyM' z#ƛyM' ⟩
                      （ y ∙ x ） M'
                    ∎    )

lemma⇉βrule : {M M' N N' P : Λ}(x y : Atom)
        → ƛ x M ⇉ ƛ y M'
        → N ⇉ N'
        → M' [ y ≔ N' ] ∼α P
        → Σ Λ (λ M″ → ƛ x M ⇉ ƛ x M″ × M″ [ x ≔ N' ] ∼α P)
lemma⇉βrule {M} {M'} {N} {N'} {P} x y ƛxM⇉ƛyM' N⇉N' M'[y≔N']∼P
  =  （ y ∙ x ） M'                              ,
     lemma⇉αright  ƛxM⇉ƛyM' (lemma∼αλ' x#ƛyM')  ,
     (  begin
          (（ y ∙ x ） M') [ x ≔ N' ]
        ≈⟨  cong (λ H → H [ x ≔ N' ]) (lemma∙comm {y} {x} {M'}) ⟩
          (（ x ∙ y ） M') [ x ≔ N' ]
        ∼⟨ lemmaSwapSubstVar' x y N' M' x#ƛyM' ⟩
          M' [ y ≔ N' ]
        ∼⟨ M'[y≔N']∼P  ⟩
          P
        ∎    )
  where
  x#ƛyM' : x # ƛ y M'
  x#ƛyM' = lemma⇉# #ƛ≡ ƛxM⇉ƛyM'
\end{code}

\begin{code}
P⇉[] : {N N' : Λ}(x : Atom) → Λ → Set
P⇉[] {N} {N'} x M = {M' : Λ} → M ⇉ M' → N ⇉ N' → M [ x ≔ N ] ⇉ M' [ x ≔ N' ]

αCompP⇉[] : {N N' : Λ}(x : Atom) → αCompatiblePred (P⇉[] {N} {N'} x)
αCompP⇉[] {N} {N'} x {M} {P} M∼P P⇉[]M {M'} P⇉M' N⇉N'
  = subst (λ H → H ⇉ (M' [ x ≔ N' ])) (lemmaSubst1 N x M∼P) (P⇉[]M (lemma⇉αleft M∼P P⇉M') N⇉N')

lemma⇉Subst : {N N' : Λ}(x : Atom)(M : Λ) → P⇉[] {N} {N'} x M
lemma⇉Subst {N} {N'} x M
  = TermαPrimInd2  (P⇉[] {N} {N'} x)
                   (x ∷ fv N ++ fv N')
                   (αCompP⇉[] {N} {N'} x)
                   lemmav
                   lemma·
                   lemmaƛ
                   M
  where
  lemmav : (a : Atom) → P⇉[] {N} {N'} x (v a)
  lemmav a (⇉v .a) N⇉N' with x ≟ₐ a
  ... | yes  _ = N⇉N'
  ... | no   _ = ⇉v a
  lemma· : (P Q : Λ)
    → P⇉[] {N} {N'} x P
    → P⇉[] {N} {N'} x Q
    → ((c : Atom) → c ∈ x ∷ fv N ++ fv N' → c ∉b P · Q)
    → P⇉[] {N} {N'} x (P · Q)
  lemma· P Q hiP hiQ f∉ .{P' · Q'}
         (⇉· .{P} {P'} .{Q} {Q'} P⇉P' Q⇉Q')
         N⇉N'
    = ⇉· (hiP P⇉P' N⇉N') (hiQ Q⇉Q' N⇉N')
  lemma· (ƛ .y P) Q hiƛyP hiQ f∉ {M'}
         (⇉β .{P} {P'} .{Q} {Q'} .{M'} y z (⇉ƛ xs ∀w∉xs（yw）P⇉（zw）P') Q⇉Q' P'[z≔Q']∼M')
         N⇉N'
    with lemma⇉βrule y z (⇉ƛ xs ∀w∉xs（yw）P⇉（zw）P') Q⇉Q' P'[z≔Q']∼M'
  ... | P″ , ƛyP⇉ƛyP″ , P″[y≔N']∼M'
    = lemma⇉αleft
            (  begin
                 ((ƛ y P) · Q) [ x ≔ N ]
               ≈⟨ refl ⟩
                 (ƛ y P) [ x ≔ N ] · Q [ x ≔ N ]
               ∼⟨ ∼α· (lemmaƛ∼[] P y∉x∷fvN) ρ ⟩
                 (ƛ y (P [ x ≔ N ])) · Q [ x ≔ N ]
               ∎   )
            (⇉β  {P [ x ≔ N ]} {P″ [ x ≔ N' ]}
                 {Q [ x ≔ N ]} {Q' [ x ≔ N' ]}
                 {M' [ x ≔ N' ]} y y
                 (lemma⇉αleft  (  begin
                                    ƛ y (P [ x ≔ N ])
                                  ∼⟨ σ (lemmaƛ∼[] P y∉x∷fvN) ⟩
                                    (ƛ y P) [ x ≔ N ]
                                  ∎                    )
                               (lemma⇉αright  (hiƛyP ƛyP⇉ƛyP″ N⇉N')
                                              (  begin
                                                   (ƛ y P″) [ x ≔ N' ]
                                                 ∼⟨ lemmaƛ∼[] P″ y∉x∷fvN' ⟩
                                                   ƛ y (P″ [ x ≔ N' ])
                                                 ∎                      )))
                 (hiQ Q⇉Q' N⇉N')
                 (  begin
                      (P″ [ x ≔ N' ]) [ y ≔ Q' [ x ≔ N' ] ]
                    ∼⟨ σ (lemmaSubstComposition Q' P″ y∉x∷fvN') ⟩
                      (P″ [ y ≔ Q' ]) [ x ≔ N' ]
                    ≈⟨ lemmaSubst1 N' x P″[y≔N']∼M' ⟩
                      M' [ x ≔ N' ]
                    ∎                                         )            )
    where
    y∉x∷fvN++fvN' : y ∉ x ∷ (fv N ++ fv N')
    y∉x∷fvN++fvN' y∈x∷fvN++fvN' with f∉ y y∈x∷fvN++fvN'
    ... | ∉b· (∉bƛ y≢y _) _ = ⊥-elim (y≢y refl)
    y∉x∷fvN : y ∉ x ∷ fv N
    y∉x∷fvN = ∉-∷⁺ (∉-∷⁼ (here refl) y∉x∷fvN++fvN') (∉-++⁻ˡ (fv N) (∉-++⁻ʳ [ x ] y∉x∷fvN++fvN'))
    y∉x∷fvN' : y ∉ x ∷ fv N'
    y∉x∷fvN' = ∉-∷⁺ (∉-∷⁼ (here refl) y∉x∷fvN++fvN') (∉-++⁻ʳ (fv N) (∉-++⁻ʳ [ x ] y∉x∷fvN++fvN'))
  lemmaƛ : (P : Λ) (b : Atom)
    → P⇉[] {N} {N'} x P
    → ((c : Atom) → c ∈ x ∷ fv N ++ fv N' → c ∉b ƛ b P)
    → P⇉[] {N} {N'} x (ƛ b P)
  lemmaƛ P b hiP f∉ {Q} ⇉ƛbP⇉Q N⇉N'
    with lemma⇉ƛrule ⇉ƛbP⇉Q
  ... | P″ , P⇉P″ ,  ƛbP⇉ƛbP″ , Q∼ƛbP″
    = lemma⇉αright  (lemma⇉αleft (lemmaƛ∼[] P b∉x∷fvN) (lemma⇉ƛpres {b} (hiP P⇉P″ N⇉N')))
                    (  begin
                         ƛ b (P″ [ x ≔ N' ])
                       ∼⟨ σ (lemmaƛ∼[] P″ b∉x∷fvN')    ⟩
                         (ƛ b P″)  [ x ≔ N' ]
                       ≈⟨ lemmaSubst1 N' x (σ Q∼ƛbP″)  ⟩
                         Q         [ x ≔ N' ]
                       ∎  )
    where
    b∉x∷fvN++fvN' : b ∉ x ∷ (fv N ++ fv N')
    b∉x∷fvN++fvN' b∈x∷fvN++fvN' with f∉ b b∈x∷fvN++fvN'
    ... | ∉bƛ b≢b _ = ⊥-elim (b≢b refl)
    b∉x∷fvN : b ∉ x ∷ fv N
    b∉x∷fvN = ∉-∷⁺ (∉-∷⁼ (here refl) b∉x∷fvN++fvN') (∉-++⁻ˡ (fv N) (∉-++⁻ʳ [ x ] b∉x∷fvN++fvN'))
    b∉x∷fvN' : b ∉ x ∷ fv N'
    b∉x∷fvN' = ∉-∷⁺ (∉-∷⁼ (here refl) b∉x∷fvN++fvN') (∉-++⁻ʳ (fv N) (∉-++⁻ʳ [ x ] b∉x∷fvN++fvN'))
\end{code}
