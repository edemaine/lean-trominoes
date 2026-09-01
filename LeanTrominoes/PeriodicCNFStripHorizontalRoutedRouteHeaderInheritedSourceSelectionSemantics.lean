/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Inherited source selection from copied Figure 9 blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderInheritedSourceSelection

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderCopiedSourcePosition

/-- Retain exactly the values aligned with inherited scope controls. -/
def selectedInheritedValues {Value : Type} :
    List AtomScopeControl → List Value → List Value
  | [], _ => []
  | _, [] => []
  | .inherited _ :: scopes, value :: values =>
      value :: selectedInheritedValues scopes values
  | .parentLocal _ :: scopes, _ :: values =>
      selectedInheritedValues scopes values

private theorem selectedInheritedValues_append
    {Value : Type} (firstScopes secondScopes : List AtomScopeControl)
    (firstValues secondValues : List Value)
    (lengthEq : firstScopes.length = firstValues.length) :
    selectedInheritedValues (firstScopes ++ secondScopes)
        (firstValues ++ secondValues) =
      selectedInheritedValues firstScopes firstValues ++
        selectedInheritedValues secondScopes secondValues := by
  induction firstScopes generalizing firstValues with
  | nil =>
      cases firstValues with
      | nil => rfl
      | cons value values => simp at lengthEq
  | cons scope scopes induction =>
      cases firstValues with
      | nil => simp at lengthEq
      | cons value values =>
          have tailLength : scopes.length = values.length := by
            simpa using Nat.succ.inj lengthEq
          cases scope <;>
            simp [selectedInheritedValues,
              induction values tailLength]

theorem selectedInheritedValues_map
    {Value Output : Type} (mapValue : Value → Output)
    (scopes : List AtomScopeControl) (values : List Value) :
    selectedInheritedValues scopes (values.map mapValue) =
      (selectedInheritedValues scopes values).map mapValue := by
  induction scopes generalizing values with
  | nil => rfl
  | cons scope scopes induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases scope <;>
            simp [selectedInheritedValues, induction]

theorem selectedInheritedValues_forall
    {Value : Type} (predicate : Value → Prop)
    (scopes : List AtomScopeControl) (values : List Value)
    (all : values.Forall predicate) :
    (selectedInheritedValues scopes values).Forall predicate := by
  induction scopes generalizing values with
  | nil => simp [selectedInheritedValues]
  | cons scope scopes induction =>
      cases values with
      | nil => simp [selectedInheritedValues]
      | cons value values =>
          rw [List.forall_cons] at all
          cases scope <;>
            simp [selectedInheritedValues, all.1,
              induction values all.2]

/-- In one finite routed Figure 9 block, inherited source offsets never
repeat.  Binary and ternary blocks may retain a proper subset of slots. -/
private theorem selected_clauseBlock_scopeOffsets_nodup
    (profile : DirectedClauseProfile) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map scopeOffset)).Nodup := by
  cases profile <;> native_decide +revert

private theorem selected_clauseBlock_scopeOffsets_forall_lt
    (profile : DirectedClauseProfile) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map scopeOffset)).Forall fun offset =>
      offset < sourceWordCount profile := by
  cases profile <;> native_decide +revert

private theorem selected_clauseBlock_positions_nodup
    (start : Nat) (profile : DirectedClauseProfile) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map fun scope => start + scopeOffset scope)).Nodup := by
  have mapEq :
      (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map (fun scope => start + scopeOffset scope) =
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map scopeOffset).map (fun offset => start + offset) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro scope scopeMember
    rfl
  rw [mapEq, selectedInheritedValues_map]
  exact (selected_clauseBlock_scopeOffsets_nodup profile).map
    (fun _ _ equality => Nat.add_left_cancel equality)

private theorem selected_clauseBlock_positions_forall_lt
    (start : Nat) (profile : DirectedClauseProfile) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile)
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map fun scope => start + scopeOffset scope)).Forall
      fun position => position < start + sourceWordCount profile := by
  rw [List.forall_iff_forall_mem]
  intro position positionMember
  have mapEq :
      (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map (fun scope => start + scopeOffset scope) =
        ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
          profile).map scopeOffset).map (fun offset => start + offset) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro scope scopeMember
    rfl
  rw [mapEq, selectedInheritedValues_map] at positionMember
  rcases List.mem_map.mp positionMember with
    ⟨offset, offsetMember, rfl⟩
  have offsetLt := (List.forall_iff_forall_mem.mp
    (selected_clauseBlock_scopeOffsets_forall_lt profile))
      offset offsetMember
  omega

private theorem expectedAux_forall_ge
    (start : Nat) (source : List Token) :
    (expectedAux start source).Forall fun position => start <= position := by
  induction source generalizing start with
  | nil => simp [expectedAux]
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [expectedAux] using induction start
      | clause profile =>
          rw [expectedAux, List.forall_append]
          constructor
          · rw [List.forall_iff_forall_mem]
            intro position positionMember
            rcases List.mem_map.mp positionMember with
              ⟨scope, scopeMember, rfl⟩
            omega
          · exact (induction (start + sourceWordCount profile)).imp
              (fun position lower => by omega)

private theorem selected_expectedAux_nodup
    (start : Nat) (source : List Token) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
        (expectedAux start source)).Nodup := by
  induction source generalizing start with
  | nil => simp [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
      expectedAux, selectedInheritedValues]
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            expectedAux] using induction start
      | clause profile =>
          let scopes :=
            HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
              profile
          have blockLength :
              scopes.length =
                (scopes.map fun scope => start + scopeOffset scope).length := by
            simp
          simp only [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            List.flatMap_cons, expectedAux]
          rw [selectedInheritedValues_append _ _ _ _ blockLength,
            List.nodup_append]
          refine ⟨selected_clauseBlock_positions_nodup start profile,
            induction (start + sourceWordCount profile), ?_⟩
          have firstLt :=
            selected_clauseBlock_positions_forall_lt start profile
          have secondGe := selectedInheritedValues_forall
            (fun position => start + sourceWordCount profile <= position)
            (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
            (expectedAux (start + sourceWordCount profile) source)
            (expectedAux_forall_ge
              (start + sourceWordCount profile) source)
          intro first firstMember second secondMember equality
          have firstBound := (List.forall_iff_forall_mem.mp firstLt)
            first firstMember
          have secondBound := (List.forall_iff_forall_mem.mp secondGe)
            second secondMember
          omega

/-- The implemented copied source-position compiler remains duplicate-free
after discarding all parent-local final outputs. -/
theorem selectedInheritedValues_positions_nodup (source : List Token) :
    (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
        (positions source)).Nodup := by
  rw [positions_eq_expected]
  exact selected_expectedAux_nodup 0 source

end HorizontalRoutedRouteHeaderInheritedSourceSelection
end PeriodicCNFStripReduction
end LeanTrominoes

end
