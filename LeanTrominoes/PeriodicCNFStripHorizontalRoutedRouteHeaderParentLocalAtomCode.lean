/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Pairing
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderAtomScopeData

/-! # Canonical finite codes for parent-local final atoms -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

/-- The custom finite comparator on atom controls is ordinary equality of
their explicit represented parent-relative atoms. -/
theorem AtomControl.sameAtom_eq_decide_representedAtom
    (first second : AtomControl) :
    first.sameAtom second =
      decide (first.representedAtom = second.representedAtom) := by
  cases first <;> cases second <;>
    simp [AtomControl.sameAtom, AtomControl.representedAtom]

/-- Identify the multiple finite descriptors that can select the same local
Figure 9 atom. -/
def parentLocalAtomSetoid : Setoid AtomControl where
  r first second := first.representedAtom = second.representedAtom
  iseqv := {
    refl := fun _ => rfl
    symm := fun equality => equality.symm
    trans := fun first second => first.trans second
  }

instance parentLocalAtomSetoidDecidableRel :
    DecidableRel parentLocalAtomSetoid.r := by
  intro first second
  change Decidable (first.representedAtom = second.representedAtom)
  infer_instance

/-- Canonical finite equality class of a parent-local Figure 9 or polarity
atom. -/
abbrev ParentLocalAtomCode := Quotient parentLocalAtomSetoid

noncomputable instance : Fintype ParentLocalAtomCode :=
  Quotient.fintype parentLocalAtomSetoid

instance : Inhabited ParentLocalAtomCode :=
  ⟨Quotient.mk parentLocalAtomSetoid default⟩

def parentLocalAtomCode (control : AtomControl) : ParentLocalAtomCode :=
  Quotient.mk parentLocalAtomSetoid control

theorem parentLocalAtomCode_eq_iff (first second : AtomControl) :
    parentLocalAtomCode first = parentLocalAtomCode second ↔
      first.representedAtom = second.representedAtom := by
  change Quotient.mk parentLocalAtomSetoid first =
      Quotient.mk parentLocalAtomSetoid second ↔ _
  rw [Quotient.eq_iff_equiv]
  rfl

/-- Quotient-code equality is exactly the established finite atom
comparator, so no descriptor-dependent distinction remains. -/
theorem AtomControl.sameAtom_eq_decide_parentLocalAtomCode
    (first second : AtomControl) :
    first.sameAtom second =
      decide (parentLocalAtomCode first = parentLocalAtomCode second) := by
  rw [AtomControl.sameAtom_eq_decide_representedAtom]
  exact Bool.decide_congr
    (parentLocalAtomCode_eq_iff first second).symm

/-- Fixed finite enumeration index used only inside the self-delimiting local
atom word below. -/
noncomputable def parentLocalAtomCodeIndex
    (code : ParentLocalAtomCode) : Nat :=
  (Fintype.equivFin ParentLocalAtomCode code).val

theorem parentLocalAtomCodeIndex_injective :
    Function.Injective parentLocalAtomCodeIndex := by
  intro first second equality
  apply (Fintype.equivFin ParentLocalAtomCode).injective
  apply Fin.ext
  exact equality

@[simp] theorem parentLocalAtomCodeIndex_eq_iff
    (first second : ParentLocalAtomCode) :
    parentLocalAtomCodeIndex first = parentLocalAtomCodeIndex second ↔
      first = second :=
  parentLocalAtomCodeIndex_injective.eq_iff

/-- Semantic source of a globally separating final-atom word.  Inherited
atoms reuse an already separating pre-Figure9 word; local atoms use their
parent clause index and canonical finite local code. -/
inductive ScopedAtomWordSource
  | inherited (sourceWord : List Bool)
  | parentLocal (parentIndex : Nat) (code : ParentLocalAtomCode)

/-- A leading bit separates inherited from local atoms.  A local atom's
remaining all-true length is the injective pairing of its parent and finite
code. -/
noncomputable def ScopedAtomWordSource.word :
    ScopedAtomWordSource → List Bool
  | .inherited sourceWord => false :: sourceWord
  | .parentLocal parentIndex code =>
      true :: List.replicate
        (Nat.pair parentIndex (parentLocalAtomCodeIndex code)) true

/-- Equality of scoped sources is exactly equality of their binary words,
assuming the inherited source words already separate their atoms. -/
theorem ScopedAtomWordSource.word_eq_iff
    (first second : ScopedAtomWordSource) :
    first.word = second.word ↔
      match first, second with
      | .inherited firstWord, .inherited secondWord =>
          firstWord = secondWord
      | .parentLocal firstParent firstCode,
          .parentLocal secondParent secondCode =>
          firstParent = secondParent ∧ firstCode = secondCode
      | _, _ => False := by
  cases first <;> cases second <;>
    simp [ScopedAtomWordSource.word, Nat.pair_eq_pair]

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes

end
