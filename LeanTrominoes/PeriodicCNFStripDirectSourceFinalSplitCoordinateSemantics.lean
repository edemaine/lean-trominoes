/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSplitCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedRingVariableSemantics

/-! # Refined coordinates of the actual copied-clause literals -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit PeriodicThreeSATThree
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance splitCopiedCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

private theorem copied_atoms {Atom : Type} [DecidableEq Atom] (source : PeriodicCNF Atom) :
    (copiedOccurrenceClauses source).flatMap (fun clause => clause.literals.map PeriodicLiteral.atom) =
      selectedCopies (retainedFinalCoordinatedScaledSource source).erase
        (occurrencePortsForFigureSeven source) := by
  rw [← PeriodicEightOccurrenceSplit.occurrenceClauses_variableOccurrences]
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]
  unfold copiedOccurrenceClauses copiedOccurrenceClause
  simp only [PeriodicCNF.variableOccurrences, PeriodicEightOccurrenceSplit.occurrenceClauses,
    PositionedPeriodicCNF.erase, List.zipIdx_map, List.map_map, List.flatMap_map,
    Function.comp_def, Prod.map, id_eq]

/-- The compiler's ring copies are exactly the literals in the geometric
copied-clause prefix, including the compass rotation of angular ranks. -/
theorem directSourceFinalSplitCoordinateCopies_eq_copied_atoms (symbols : List encoding.Γ) :
    directSourceFinalSplitCoordinateCopies decider symbols =
      (copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap
        (fun clause => clause.literals.map PeriodicLiteral.atom) := by
  rw [copied_atoms]
  change _ = selectedCopies
    (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
    (occurrencePortsOfAngularOrder
      (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
      (angularOccurrenceOrder
        (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols))))
  rw [selectedCopies_eq_boundedGlobalStableAtomRankPairs _ _
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
    (directSourceFinalScaledSource_occurrencesAtMostEight decider symbols)]
  simp only [directSourceFinalSplitCoordinateCopies, directSourceFinalCoordinateOccurrences,
    directSourceFinalCoordinateOccurrenceSlot, retainedOccurrenceGlobalBoundedStableAtomRankPairs,
    List.map_map, Function.comp_def]

/-- All four compiled columns give the actual placement of every copied
literal in its clause and literal presentation order. -/
theorem directSourceFinalSplitCoordinates_eq_copied_positions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalSplitCoordinates decider horizontal keepPositive symbols =
      (copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap fun clause =>
        clause.literals.map fun literal =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              (directSourceFormula decider symbols)).position literal.atom) := by
  rw [directSourceFinalSplitCoordinates_eq_positions,
    directSourceFinalSplitCoordinateCopies_eq_copied_atoms, List.map_flatMap]
  simp only [List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction
end
