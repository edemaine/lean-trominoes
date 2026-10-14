/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedAtoms
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFreshAtomHorizontalSemantics

/-! # Actual original atoms selected by direct Figure 9 occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

theorem prefixAtom_eq_localQuery
    (routePrefix : HorizontalRoutedRouteHeader.PrefixDescriptor) :
    HorizontalRoutedRouteHeader.prefixAtom routePrefix =
      ((templateDrawingOfClauseProfile routePrefix.localQuery.1).incidenceAt
        routePrefix.localQuery.2).literal.1 := by
  cases routePrefix <;> rfl

private theorem originalOperation_of_not_fresh (occurrence : SourceOccurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) :
    occurrence.header.polarity.operation = .compatible ∨
      occurrence.header.polarity.operation = .complementOriginal := by
  cases operation : occurrence.header.polarity.operation <;>
    simp_all [sourceOccurrenceIsFresh]

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance originalHorizontalVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- A proof-side witness for the coherent record at any genuine direct index. -/
noncomputable def directSourceFinalOccurrenceWitness
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length) :
    OccurrenceWitness (directSourceFormula decider symbols)
      (directSourceFinalOccurrences decider symbols)[index] :=
  Classical.choice (occurrenceWitness (directSourceFormula decider symbols)
    (sourceFormula_widthAtMostThree (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))
    (sourceFormula_clausesNonempty (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))
    _ (List.getElem_mem indexLt))

/-- The actual pre-polarity atom obtained by instantiating the record's
finite template role in its own parent metadata. -/
noncomputable def directSourceFinalOriginalAtom
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length) :=
  let witness := directSourceFinalOccurrenceWitness decider symbols index indexLt
  instantiatedVariableMap witness.metadata.sourceClauseIndex
    witness.metadata.figureNineClauseStart witness.metadata.sourceClause
    (HorizontalRoutedRouteHeader.prefixAtom
      (directSourceFinalOccurrences decider symbols)[index].header.figurePrefix)

/-- Every original horizontal incidence is the same instantiated atom that
its coherent header selects, through final ordering, gauge, and refinement. -/
theorem directSourceFinalOriginalAtom_eq_horizontal
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (original : ¬ sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[index])
    (atom : RoutedVariable)
    (atomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    atom = .inl (directSourceFinalOriginalAtom decider symbols index indexLt) := by
  let witness := directSourceFinalOccurrenceWitness decider symbols index indexLt
  have sourceLocal : (directSourceFormula decider symbols).IsLocal :=
    sourceFormula_isLocal (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)
  have sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3 :=
    sourceFormula_widthAtMostThree (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)
  have sourceOccurrences :
      @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
        (by infer_instance) 3 (directSourceFormula decider symbols) := by
    exact PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))
  have sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [] :=
    sourceFormula_clausesNonempty (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)
  have gaugedEq : directSourceFinalGaugedFormula decider symbols =
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty := by
    rfl
  have decoded := directSourceFinalOccurrence_atom_eq_of_horizontal_lookup
    decider symbols index indexLt atom atomLookup
  rw [gaugedEq] at decoded
  have selected := witness.originalPolarityAtom sourceLocal sourceWidth sourceOccurrences sourceNonempty
    (originalOperation_of_not_fresh _ original) atom decoded
  simpa only [directSourceFinalOriginalAtom, prefixAtom_eq_localQuery, witness] using selected

end LeanTrominoes.PeriodicCNFStripReduction

end
