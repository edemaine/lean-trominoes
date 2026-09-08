/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedIncidenceElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceCoreMultiplicity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics
import LeanTrominoes.ListZipWithProject

/-! # Clause-incidence codes agree with actual horizontal typed references -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The finite compiler tag is the structural code of the actual typed
clause reference at clause zero. -/
theorem clauseIncidenceReferenceTag_eq_typed
    (set : X3CClauseSet) (color : WireColor) :
    clauseIncidenceReferenceTag set color = TypedElementCode.clauseReferenceTag set color := by
  cases set <;> cases color <;> rfl

/-- Each compiled 27-reference block codes its actual typed clause triples. -/
theorem finalClauseIncidenceElementCodeBlock_eq_typed
    (index : Nat) (fan : ClauseRibbonFanData) :
    finalClauseIncidenceElementCodeBlock index fan =
      TypedElementCode.clauseIncidenceBlock index := by
  rw [finalClauseIncidenceElementCodeBlock_eq_map]
  unfold finalClauseIncidenceElementTagBlock TypedElementCode.clauseIncidenceBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro set _
  simp only [List.map_cons, List.map_nil, incidenceColors,
    clauseIncidenceReferenceTag_eq_typed, directSourceFinalElementCodeStride]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete clause-incidence code suffix references the actual typed
horizontal elements, independently of how variable occurrence keys are named. -/
theorem directSourceFinalClauseIncidenceElementCodes_eq_horizontalTyped
    (symbols : List encoding.Γ) (key : RoutedVariable × OccurrenceSlot → Nat) :
    directSourceFinalClauseIncidenceElementCodes decider symbols =
      (clauseTriples (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        (fun triple => incidenceColors.map fun color => TypedElementCode.reference key
          (tripleReferences (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase triple) color) := by
  rw [TypedElementCode.clauseTriples_codes_eq,
    directSourceFinalClauseIncidenceElementCodes_eq_blocks]
  have blockEq : finalClauseIncidenceElementCodeBlock =
      (fun index (_ : ClauseRibbonFanData) => TypedElementCode.clauseIncidenceBlock index) := by
    funext index fan
    exact finalClauseIncidenceElementCodeBlock_eq_typed index fan
  rw [blockEq]
  rw [List.zipWith_project_left_of_length_eq TypedElementCode.clauseIncidenceBlock
    (List.range (directSourceFinalClauseFans decider symbols).length)
    (directSourceFinalClauseFans decider symbols) (by simp)]
  change (List.range (directSourceFinalClauseFans decider symbols).length).flatMap
      TypedElementCode.clauseIncidenceBlock = _
  rw [directSourceFinalClauseFans_length_eq_horizontalTypedClauses]
  unfold horizontalThreeDMTypedSourceComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]

end LeanTrominoes.PeriodicCNFStripReduction

end
