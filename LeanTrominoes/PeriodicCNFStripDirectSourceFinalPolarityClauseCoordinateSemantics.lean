/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateCompiler
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSourceIndexedClausePositions
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedAtoms

/-! # Exact polarity clause coordinates selected by each source occurrence -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader PeriodicOneInThreePolarityNormalizationRouteSubdivision

private theorem exists_positionedClause_of_erased_lookup {Variable : Type}
    (source : PositionedPeriodicCNF Variable) {index : Nat} {clause : PeriodicClause Variable}
    (lookup : source.erase.clauses[index]? = some clause) :
    ∃ positionedClause, source.clauses[index]? = some positionedClause := by
  rw [PositionedPeriodicCNF.erase, List.getElem?_map] at lookup
  obtain ⟨positionedClause, member, _⟩ := Option.map_eq_some_iff.mp lookup
  exact ⟨positionedClause, member⟩

private theorem clausePosition_affine {Variable : Type}
    (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header)
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (index : Nat) (clause : PositionedPeriodicClause Variable) (origin : Cell)
    (lookup : source.clauses[index]? = some clause)
    (position : clause.position = Cell.scale 3 origin)
    (second : (refinedRoute routes index header.polarity.indexed.sourceLiteralIndex).getD 2 (0, 0) =
      Cell.add (Cell.scale 3 origin) (Cell.scale 2 (sourceFirstDirection header).step)) :
    (sourceIndexedDescriptorOf index header.polarity.indexed).clausePosition source routes =
      Cell.add (Cell.scale 3 origin) (polarityClauseOffset header) := by
  cases operation : header.polarity.operation <;>
    simp only [SourceIndexedDescriptor.clausePosition, sourceIndexedDescriptorOf,
      ClauseProfilePolarityRouteOperation.Descriptor.indexed, operation, polarityClauseOffset]
  · rw [List.getD_eq_getElem?_getD, lookup, Option.getD_some, position]
    simp [Cell.add]
  · rw [List.getD_eq_getElem?_getD, lookup, Option.getD_some, position]
    simp [Cell.add]
  · exact second
  · exact second

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance polarityClauseSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- A successful actual incidence decoder supplies the refined source
members needed to identify the affine clause coordinate. -/
theorem directSourceFinalPolarityClauseCoordinates_descriptor_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (sourceLocal : (directSourceFormula decider symbols).IsLocal)
    (sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3)
    (sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols))
    (sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [])
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (atom : RoutedVariable)
    (decoded : (sourceIndexedDescriptorOf occurrence.generatedClauseIndex occurrence.header.polarity.indexed).atom?
      (refinedSource
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols))).erase = some atom) :
    (directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((sourceIndexedDescriptorOf occurrence.generatedClauseIndex occurrence.header.polarity.indexed).clausePosition
          (refinedSource
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
              (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty)
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
              (directSourceFormula decider symbols)))
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
            (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty))) := by
  obtain ⟨erasedClause, clauseLookup, decodedLiteral⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨refinedLiteral, literalLookup, _⟩ := Option.map_eq_some_iff.mp decodedLiteral
  obtain ⟨sourceClause, sourceLiteral, clauseMember, literalMember, _⟩ :=
    exists_sourceLiteral_of_refinedSource_lookup _ _ clauseLookup literalLookup
  have second := (witness.polaritySubdivisionPositions sourceLocal sourceWidth sourceOccurrences sourceNonempty
    sourceClause clauseMember sourceLiteral literalMember).2
  obtain ⟨refinedClause, refinedLookup⟩ := exists_positionedClause_of_erased_lookup _ clauseLookup
  obtain ⟨originalClause, originalMember, positionEq⟩ := exists_sourceClause_of_refinedSource_clause_mem _ _
    (List.mk_mem_zipIdx_iff_getElem?.mpr refinedLookup)
  rw [witness.finalGaugedClausePosition sourceLocal sourceWidth sourceOccurrences sourceNonempty
    originalClause originalMember] at positionEq
  have coordinates := directSourceFinalPolarityClauseCoordinates_lookup decider horizontal keepPositive symbols
    index occurrence lookup witness
  have pointEq := clausePosition_affine occurrence.header _ _ occurrence.generatedClauseIndex
    refinedClause witness.metadata.clause.position refinedLookup positionEq second
  rw [pointEq]
  exact coordinates

end LeanTrominoes.PeriodicCNFStripReduction
end
