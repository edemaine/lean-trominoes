/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionData
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockStartFixed

/-! # Stable indexed blocks of retained Figure 9 cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open OccurrenceSplitRing
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Renaming and positioning a local Figure 7 clause does not change its
finite literal profiles. -/
theorem scaledPositionedLocalCycleClause_ofClause_eq_localCycleClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : EmbeddedClause RingVertex) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        routes clauseIndex
        ((positionedLocalCycleClause
            (placementScaledForFigureSeven source) atom clause).scale
          retainedTerminalFanRoutingRefinement) =
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        routes clauseIndex
        (FormulaShapeFixedEightDirection.localCycleClause clause) := by
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
    FormulaShapeFixedEightDirection.localCycleClause
    positionedLocalCycleClause periodicCycleClause
  rw [PositionedPeriodicClause.scale_literals,
    List.zipIdx_map, List.zipIdx_map, List.map_map, List.map_map]
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.map_congr_left
  rintro ⟨literal, literalIndex⟩ _literalMember
  rfl

/-- The scaled final implication-cycle suffix is a fixed-width flat map over
the stable source-variable enumeration. -/
theorem finalCycleClauses_eq_flatMap_scaledCycleBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    finalCycleClauses source =
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).flatMap fun atom =>
        (PeriodicEightOccurrenceSplitPositioned.cycleClausesFor
            (placementScaledForFigureSeven source) atom).map
          (PositionedPeriodicClause.scale
            retainedTerminalFanRoutingRefinement) := by
  unfold finalCycleClauses
    PeriodicEightOccurrenceSplitPositioned.allCycleClauses
  rw [List.map_flatMap]

/-- Looking up a final route at an affine cycle-block index is definitionally
the same as using the corresponding local index route family. -/
theorem finalRoute_ofClause_eq_routedCycleRoutesAt
    {Variable ClauseVariable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomIndex localClauseIndex : Nat)
    (clause : PositionedPeriodicClause ClauseVariable) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source +
          (FormulaShapeFixedEight.copiesPerVariable * atomIndex +
            localClauseIndex))
        clause =
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (routedCycleRoutesAt source atomIndex)
        localClauseIndex clause := by
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.map_congr_left
  rintro ⟨literal, literalIndex⟩ _literalMember
  rfl

/-- One scaled positioned cycle block, indexed from its fixed-width global
offset, produces the corresponding index-based local descriptor block. -/
theorem scaledCycleBlockDescriptors_eq_at
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomIndex : Nat) :
    (((PeriodicEightOccurrenceSplitPositioned.cycleClausesFor
          (placementScaledForFigureSeven source) atom).map
        (PositionedPeriodicClause.scale
          retainedTerminalFanRoutingRefinement)).zipIdx
      (FormulaShapeFixedEight.copiesPerVariable * atomIndex)).map
        (fun taggedClause =>
          FormulaShapeDirectionOrdering.Token.clause
            (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
              (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                source)
              (copiedClauseCount source + taggedClause.2)
              taggedClause.1)) =
      routedCycleClauseDescriptorsAt source atomIndex := by
  unfold routedCycleClauseDescriptorsAt
  rw [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor_eq_cycleFormula,
    List.map_map,
    FormulaShapeFixedEightDirection.localCycleFormula,
    List.zipIdx_map, List.zipIdx_map, List.map_map, List.map_map]
  rw [List.zipIdx_eq_map_add, List.map_map]
  apply List.map_congr_left
  rintro ⟨clause, localClauseIndex⟩ _localClauseMember
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  change
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source +
          (FormulaShapeFixedEight.copiesPerVariable * atomIndex +
            localClauseIndex))
        ((positionedLocalCycleClause
            (placementScaledForFigureSeven source) atom clause).scale
          retainedTerminalFanRoutingRefinement) =
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (routedCycleRoutesAt source atomIndex)
        localClauseIndex
        (FormulaShapeFixedEightDirection.localCycleClause clause)
  rw [finalRoute_ofClause_eq_routedCycleRoutesAt]
  exact scaledPositionedLocalCycleClause_ofClause_eq_localCycleClause
    source atom (routedCycleRoutesAt source atomIndex)
    localClauseIndex clause

/-- The global routed cycle suffix is exactly the concatenation of the local
Figure 7 descriptor blocks at their stable source-variable indices. -/
theorem routedCycleClauseDescriptors_eq_indexedBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedCycleClauseDescriptors source =
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).zipIdx.flatMap
        (fun taggedAtom =>
          routedCycleClauseDescriptorsAt source taggedAtom.2) := by
  let atoms :=
    sourceVariables (sourceScaledForFigureSeven source).erase
  let block := fun atom =>
    (PeriodicEightOccurrenceSplitPositioned.cycleClausesFor
        (placementScaledForFigureSeven source) atom).map
      (PositionedPeriodicClause.scale
        retainedTerminalFanRoutingRefinement)
  have blockLength : ∀ atom, (block atom).length =
      FormulaShapeFixedEight.copiesPerVariable := by
    intro atom
    simp [block,
      PeriodicEightOccurrenceSplitPositioned.cycleClausesFor]
  unfold routedCycleClauseDescriptors
  rw [finalCycleClauses_eq_flatMap_scaledCycleBlocks]
  change ((atoms.flatMap block).zipIdx.map _) = _
  rw [IndexedListScan.flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
    atoms block FormulaShapeFixedEight.copiesPerVariable 0 blockLength]
  simp only [Nat.zero_add, List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨atom, atomIndex⟩ atomMember
  exact scaledCycleBlockDescriptors_eq_at source atom atomIndex

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
