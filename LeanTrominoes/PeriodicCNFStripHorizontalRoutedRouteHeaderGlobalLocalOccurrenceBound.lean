/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBound

/-! # Global occurrence bounds for parent-indexed local atoms -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderGlobalLocalAtoms

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderCopiedLocalAtomCode
open HorizontalRoutedRouteHeaderPresentationAtomScope

/-- A canonical local atom together with the globally unique index of its
parent source clause. -/
abbrev Atom := Nat × ParentLocalAtomCode

def block (parent : Nat) (profile : DirectedClauseProfile) : List Atom :=
  (parentLocalCodes profile).map fun code => (parent, code)

/-- Parent-indexed local atoms of a descriptor suffix.  Variable markers do
not make parent blocks; every clause descriptor advances the parent index. -/
def atomsAux : Nat → List Token → List Atom
  | _, [] => []
  | parent, .variable :: source => atomsAux parent source
  | parent, .clause profile :: source =>
      block parent profile ++ atomsAux (parent + 1) source

def atoms (source : List Token) : List Atom :=
  atomsAux 0 source

private theorem block_count_self (parent : Nat)
    (profile : DirectedClauseProfile) (code : ParentLocalAtomCode) :
    (block parent profile).count (parent, code) =
      (parentLocalCodes profile).count code := by
  unfold block
  rw [List.count_map_of_injective
    (parentLocalCodes profile) (fun current => (parent, current))
    (fun first second equal => congrArg Prod.snd equal) code]

private theorem block_count_le_three (parent : Nat)
    (profile : DirectedClauseProfile) (code : ParentLocalAtomCode) :
    (block parent profile).count (parent, code) <= 3 := by
  rw [block_count_self]
  exact parentLocalCodes_count_le_three profile code

private theorem block_not_mem_of_parent_ne
    (parent targetParent : Nat) (profile : DirectedClauseProfile)
    (code : ParentLocalAtomCode) (different : targetParent ≠ parent) :
    (targetParent, code) ∉ block parent profile := by
  intro member
  unfold block at member
  rcases List.mem_map.mp member with
    ⟨current, _currentMember, equal⟩
  exact different (congrArg Prod.fst equal).symm

/-- Every atom in a suffix has a parent at or after the supplied starting
index. -/
theorem parent_le_of_mem_atomsAux (parent : Nat) (source : List Token)
    (atom : Atom) (member : atom ∈ atomsAux parent source) :
    parent <= atom.1 := by
  induction source generalizing parent with
  | nil => simp [atomsAux] at member
  | cons token source induction =>
      cases token with
      | «variable» =>
          exact induction parent (by simpa [atomsAux] using member)
      | clause profile =>
          simp only [atomsAux, List.mem_append] at member
          rcases member with blockMember | tailMember
          · unfold block at blockMember
            rcases List.mem_map.mp blockMember with
              ⟨code, _codeMember, equal⟩
            rw [← equal]
          · exact Nat.le_trans (Nat.le_succ parent)
              (induction (parent + 1) tailMember)

/-- Parent indices isolate the fixed local bound globally: no local atom can
accumulate occurrences from two different source-clause blocks. -/
theorem atomsAux_count_le_three (parent : Nat) (source : List Token)
    (target : Atom) :
    (atomsAux parent source).count target <= 3 := by
  induction source generalizing parent with
  | nil => simp [atomsAux]
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [atomsAux] using induction parent
      | clause profile =>
          rcases target with ⟨targetParent, targetCode⟩
          rw [atomsAux, List.count_append]
          by_cases parentEq : targetParent = parent
          · subst targetParent
            have tailNotMem :
                (parent, targetCode) ∉ atomsAux (parent + 1) source := by
              intro member
              have lower := parent_le_of_mem_atomsAux
                (parent + 1) source (parent, targetCode) member
              omega
            rw [List.count_eq_zero_of_not_mem tailNotMem]
            simpa using block_count_le_three parent profile targetCode
          · have blockNotMem :
                (targetParent, targetCode) ∉ block parent profile :=
              block_not_mem_of_parent_ne parent targetParent profile
                targetCode parentEq
            rw [List.count_eq_zero_of_not_mem blockNotMem]
            simpa using induction (parent + 1)

theorem atoms_count_le_three (source : List Token) (target : Atom) :
    (atoms source).count target <= 3 := by
  exact atomsAux_count_le_three 0 source target

/-- The arithmetic code used by the compiler, factored through the explicit
parent/code pair. -/
def numericCode (atom : Atom) : Nat :=
  atom.1 * codeBound + parentLocalAtomCodeIndex atom.2

theorem numericCode_injective : Function.Injective numericCode := by
  rintro ⟨firstParent, firstCode⟩ ⟨secondParent, secondCode⟩ equal
  have firstLt : parentLocalAtomCodeIndex firstCode < codeBound :=
    parentLocalAtomCodeIndex_lt firstCode
  have secondLt : parentLocalAtomCodeIndex secondCode < codeBound :=
    parentLocalAtomCodeIndex_lt secondCode
  have indexEq :
      parentLocalAtomCodeIndex firstCode =
        parentLocalAtomCodeIndex secondCode := by
    have modulo := congrArg (fun value => value % codeBound) equal
    simpa [numericCode, Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt firstLt, Nat.mod_eq_of_lt secondLt] using modulo
  have parentProducts :
      firstParent * codeBound = secondParent * codeBound := by
    change
      firstParent * codeBound + parentLocalAtomCodeIndex firstCode =
        secondParent * codeBound +
          parentLocalAtomCodeIndex secondCode at equal
    rw [indexEq] at equal
    exact Nat.add_right_cancel equal
  have parentEq : firstParent = secondParent := by
    apply Nat.mul_left_cancel codeBound_pos
    simpa [Nat.mul_comm] using parentProducts
  have codeEq : firstCode = secondCode :=
    parentLocalAtomCodeIndex_injective indexEq
  exact Prod.ext parentEq codeEq

def numericCodes (source : List Token) : List Nat :=
  (atoms source).map numericCode

/-- The injective numeric representation preserves the global local-atom
occurrence bound. -/
theorem numericCodes_count_le_three (source : List Token) (target : Nat) :
    (numericCodes source).count target <= 3 := by
  by_cases member : target ∈ numericCodes source
  · unfold numericCodes at member ⊢
    rcases List.mem_map.mp member with ⟨atom, _atomMember, rfl⟩
    rw [List.count_map_of_injective
      (atoms source) numericCode numericCode_injective atom]
    exact atoms_count_le_three source atom
  · rw [List.count_eq_zero_of_not_mem member]
    omega

end HorizontalRoutedRouteHeaderGlobalLocalAtoms
end PeriodicCNFStripReduction
end LeanTrominoes

end
