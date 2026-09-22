/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.PeriodicCNFStripNativeRouteWords
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateHorizontalSemantics
import LeanTrominoes.UnaryColumnCompiler

/-! # Actual coordinate and displacement columns under one incidence index -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PeriodicOrthocrossing DelimitedDirectionDisplacement
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeOffsetStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeOffsetVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048

abbrev nativeIncidenceRows (s : List encoding.Γ) := PositionedIncidenceRows.rows
  (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))

noncomputable def nativeOffsetVariableColumn (horizontal positive : Bool) :
    Compiler (nativeIncidenceRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (component horizontal ((horizontalRoutedPlacementComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).position row.2.1.atom))) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalHorizontalVariableCoordinatesComputableInPolyTime decider horizontal positive)
  intro s
  unfold directSourceFinalHorizontalVariableCoordinates
  rw [← PositionedIncidenceRows.atoms, List.map_map]
  cases horizontal <;> cases positive <;> rfl

noncomputable def nativeOffsetClauseColumn (horizontal positive : Bool) :
    Compiler (nativeIncidenceRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (component horizontal (PositionedPeriodicCNF.canonicalClausePosition
        (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) row.1.1))) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider horizontal positive)
  intro s
  unfold directSourceFinalHorizontalClauseCoordinates
  rw [← PositionedIncidenceRows.clausePositions, List.map_map]
  cases horizontal <;> cases positive <;> rfl

noncomputable def nativeOffsetDisplacementColumn (horizontal positive : Bool) :
    Compiler (nativeIncidenceRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (displacement horizontal (Gadget.unitSubdivisionDirections
        (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) row.1.2 row.2.2)))) := by
  apply TM2ComputableInPolyTime.of_eq (nativeRouteDisplacementCompiler decider horizontal positive)
  intro s
  rw [values_eq_displacements]
  unfold nativeRouteWords
  rw [← PositionedIncidenceRows.directionWords, List.map_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
