/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFlattenAppendPerm
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceCoreMultiplicity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExpectedParentElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceParentClauseSemantics

/-! # Complete clause-element incidence multiplicities -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM

/-- Structural terminal tags contributed by the variable side of one actual
final clause. -/
def finalClauseOccurrenceTerminalElementTagBlock
    (fan : ClauseRibbonFanData) : List Nat :=
  (finalClauseTerminalConnectorKinds fan).flatMap fun kind =>
    [(variableIncidenceClauseTerminalTag kind .red).val,
      (variableIncidenceClauseTerminalTag kind .green).val,
      (variableIncidenceClauseTerminalTag kind .blue).val]

/-- Degree expansion of the four canonical elements of one color at one
actual final clause. -/
def finalClauseCanonicalExpandedElementCodeColorBlock
    (color : WireColor) (index : Nat)
    (fan : ClauseRibbonFanData) : List Nat :=
  (List.zipWith (fun code degree => List.replicate degree code)
    (directSourceFinalClauseElementCodeBlock color index)
    (directSourceFinalClauseElementDegreeBlock fan)).flatten

/-- Degree expansion of all twelve RGB clause elements, in color-major
order within one actual final clause. -/
def finalClauseCanonicalExpandedElementCodeBlock
    (index : Nat) (fan : ClauseRibbonFanData) : List Nat :=
  finalClauseCanonicalExpandedElementCodeColorBlock .red index fan ++
    finalClauseCanonicalExpandedElementCodeColorBlock .green index fan ++
    finalClauseCanonicalExpandedElementCodeColorBlock .blue index fan

/-- The tag-level counterpart of the canonical RGB degree expansion. -/
def finalClauseCanonicalExpandedElementTagBlock
    (fan : ClauseRibbonFanData) : List Nat :=
  let degrees := directSourceFinalClauseElementDegreeBlock fan
  (List.zipWith (fun tag degree => List.replicate degree tag)
      [16, 17, 18, 19] degrees).flatten ++
    (List.zipWith (fun tag degree => List.replicate degree tag)
      [20, 21, 22, 23] degrees).flatten ++
    (List.zipWith (fun tag degree => List.replicate degree tag)
      [24, 25, 26, 27] degrees).flatten

private theorem finalClauseOccurrenceTerminalElementCodeBlock_eq_map
    (index : Nat) (fan : ClauseRibbonFanData) :
    finalClauseOccurrenceTerminalElementCodeBlock index fan =
      (finalClauseOccurrenceTerminalElementTagBlock fan).map fun tag =>
        index * directSourceFinalElementCodeStride + tag := by
  cases fan with
  | mk hasRight directions =>
      cases hasRight <;>
        simp [finalClauseOccurrenceTerminalElementCodeBlock,
          finalClauseOccurrenceTerminalElementTagBlock,
          finalClauseTerminalConnectorKinds,
          finalConnectorParentElementCodeBlock,
          variableIncidenceClauseTerminalTag]

private theorem finalClauseCanonicalExpandedElementCodeBlock_eq_map
    (index : Nat) (fan : ClauseRibbonFanData) :
    finalClauseCanonicalExpandedElementCodeBlock index fan =
      (finalClauseCanonicalExpandedElementTagBlock fan).map fun tag =>
        index * directSourceFinalElementCodeStride + tag := by
  cases fan with
  | mk hasRight directions =>
      cases hasRight <;>
        simp [finalClauseCanonicalExpandedElementCodeBlock,
          finalClauseCanonicalExpandedElementCodeColorBlock,
          finalClauseCanonicalExpandedElementTagBlock,
          directSourceFinalClauseElementCodeBlock,
          directSourceFinalClauseElementDegreeBlock,
          directSourceFinalClauseElementColorTagBase]

/-- The fixed clause core plus one occurrence-side reference to every present
terminal realizes exactly the declared degree of each canonical RGB clause
element. -/
theorem finalClauseCoreTerminalElementCodeBlock_perm_canonical
    (index : Nat) (fan : ClauseRibbonFanData) :
    (finalClauseCoreExpectedElementCodeBlock index ++
        finalClauseOccurrenceTerminalElementCodeBlock index fan).Perm
      (finalClauseCanonicalExpandedElementCodeBlock index fan) := by
  rw [finalClauseOccurrenceTerminalElementCodeBlock_eq_map,
    finalClauseCanonicalExpandedElementCodeBlock_eq_map]
  unfold finalClauseCoreExpectedElementCodeBlock
  rw [← List.map_append]
  apply List.Perm.map
  cases fan with
  | mk hasRight directions =>
      cases hasRight <;>
        native_decide +revert

private theorem zipWith_flatten_perm_of_pointwise
    {First Second Element : Type*}
    (before after : First → Second → List Element)
    (pointwise : ∀ first second,
      (before first second).Perm (after first second)) :
    ∀ (firsts : List First) (seconds : List Second),
      (List.zipWith before firsts seconds).flatten.Perm
        (List.zipWith after firsts seconds).flatten
  | [], _ => List.Perm.nil
  | _ :: _, [] => List.Perm.nil
  | first :: firsts, second :: seconds => by
      simp only [List.zipWith_cons_cons, List.flatten_cons]
      exact List.Perm.append (pointwise first second)
        (zipWith_flatten_perm_of_pointwise before after pointwise
          firsts seconds)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Canonical clause element identities repeated by their declared degrees,
in clause-major RGB order. -/
def directSourceFinalClauseExpandedElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith finalClauseCanonicalExpandedElementCodeBlock
    (List.range (directSourceFinalClauseFans decider symbols).length)
    (directSourceFinalClauseFans decider symbols)).flatten

/-- Clause-core incidences together with the variable-side parent references
contain exactly the declared number of copies of every canonical clause
element. -/
theorem directSourceFinalClauseAndParentIncidenceElementCodes_perm_canonical
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceElementCodes decider symbols ++
        directSourceFinalExpectedParentIncidenceElementCodes
          decider symbols).Perm
      (directSourceFinalClauseExpandedElementCodes decider symbols) := by
  let indices :=
    List.range (directSourceFinalClauseFans decider symbols).length
  let fans := directSourceFinalClauseFans decider symbols
  have lengths : indices.length = fans.length := by
    simp [indices, fans]
  have parentPerm :
      (directSourceFinalExpectedParentIncidenceElementCodes
          decider symbols).Perm
        (List.zipWith finalClauseOccurrenceTerminalElementCodeBlock
          indices fans).flatten := by
    apply (directSourceFinalExpectedParentIncidenceElementCodes_perm
      decider symbols).trans
    rw [directSourceFinalOccurrenceParentElementCodes_eq_clauseBlocks]
  apply (List.Perm.append
    (directSourceFinalClauseIncidenceElementCodes_perm_expected
      decider symbols)
    parentPerm).trans
  have coreProjection :
      (List.zipWith
        (fun index (_fan : ClauseRibbonFanData) =>
          finalClauseCoreExpectedElementCodeBlock index)
        indices fans).flatten =
      indices.flatMap finalClauseCoreExpectedElementCodeBlock := by
    rw [List.zipWith_project_left_of_length_eq
      finalClauseCoreExpectedElementCodeBlock indices fans lengths]
    rfl
  rw [← coreProjection]
  apply (List.zipWith_flatten_append_perm
    (fun index (_fan : ClauseRibbonFanData) =>
      finalClauseCoreExpectedElementCodeBlock index)
    finalClauseOccurrenceTerminalElementCodeBlock
    indices fans).symm.trans
  exact zipWith_flatten_perm_of_pointwise
    (fun index fan =>
      finalClauseCoreExpectedElementCodeBlock index ++
        finalClauseOccurrenceTerminalElementCodeBlock index fan)
    finalClauseCanonicalExpandedElementCodeBlock
    finalClauseCoreTerminalElementCodeBlock_perm_canonical
    indices fans

end LeanTrominoes.PeriodicCNFStripReduction

end
