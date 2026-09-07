/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.GadgetSparseRouteDirectionEndpoints
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseBlockSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockList
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanIndexedDirections
import LeanTrominoes.PositionedPeriodicCNFPresentationCanonicalRoutes

/-! # Clause fan extraction from ordered route direction blocks -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
open HorizontalRoutedRouteHeaderClauseFrame

/-- Incoming directions of the stored clause-to-variable routes, retaining
the actual clause boundaries and literal order. -/
def clauseIncomingDirectionBlocks {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List (List AxisDirection) :=
  source.clauses.zipIdx.map fun clause =>
    clause.1.literals.zipIdx.map fun literal =>
      ((unitSubdivisionDirections (routes clause.2 literal.2)).headD .invalid).opposite

theorem clauseIncomingDirectionBlocks_flatten {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (clauseIncomingDirectionBlocks source routes).flatten =
      (presentedIncidenceDirectionWords source routes).map
        (fun word => (word.headD .invalid).opposite) := by
  unfold clauseIncomingDirectionBlocks presentedIncidenceDirectionWords
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, id_eq]

theorem clauseIncomingDirectionBlocks_lengths {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (clauseIncomingDirectionBlocks source routes).map List.length =
      source.erase.clauses.map List.length := by
  simpa only [clauseIncomingDirectionBlocks, List.map_map, List.length_map,
    List.length_zipIdx, PositionedPeriodicCNF.erase, Function.comp_def] using
    congrArg (List.map fun clause : PositionedPeriodicClause Variable => clause.literals.length)
      (List.zipIdx_map_fst 0 source.clauses)

/-- Only the clause arities and incidence indices matter for these blocks. -/
theorem clauseIncomingDirectionBlocks_eq_range {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    clauseIncomingDirectionBlocks source routes =
      source.clauses.zipIdx.map fun clause =>
        (List.range clause.1.literals.length).map fun index =>
          ((unitSubdivisionDirections (routes clause.2 index)).headD .invalid).opposite := by
  unfold clauseIncomingDirectionBlocks
  apply List.map_congr_left
  intro clause _
  change clause.1.literals.zipIdx.map
      ((fun index => ((unitSubdivisionDirections (routes clause.2 index)).headD .invalid).opposite) ∘
        Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']

theorem fanOfDirections_direction (directions : List AxisDirection)
    (group : X3CClauseTerminalGroup) :
    (fanOfDirections directions).direction group =
      (directions[literalIndexOfTerminalGroup group]?).getD .north := by
  cases group <;> rfl

/-- Positive padding and anchor normalization preserve every incoming
clause direction block, including its clause and literal order. -/
theorem clauseIncomingDirectionBlocks_normalized_scale {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (factor : Nat) (positive : 0 < factor) :
    clauseIncomingDirectionBlocks
        (normalizedPositionedSource (source.scale factor) (placement.scale factor))
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) =
      clauseIncomingDirectionBlocks source routes := by
  simp only [clauseIncomingDirectionBlocks_eq_range, normalizedPositionedSource,
    PositionedPeriodicCNF.anchorNormalize, PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
    PeriodicClause.anchorNormalize_length, PositionedPeriodicClause.scale_literals]
  apply List.map_congr_left
  intro clause _
  apply List.map_congr_left
  intro index _
  simp only [PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
    unitSubdivisionDirections_scalePolyline factor positive,
    repeatDirections_headD factor positive]

/-- The direction blocks recover the complete semantic fan of every actual
clause in a planar width-three, occurrence-three source. -/
theorem clauseIncomingDirectionBlocks_fans_eq_source
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3) :
    (clauseIncomingDirectionBlocks source presentation.routes).map fanOfDirections =
      source.clauses.zipIdx.map fun clause =>
        sourceClauseRibbonFanData presentation clause.2 := by
  rw [clauseIncomingDirectionBlocks_eq_range, List.map_map]
  apply List.map_congr_left
  intro clause member
  dsimp only [Function.comp_apply]
  apply ClauseRibbonFanData.ext_fields
  · rw [sourceClauseRibbonFanData_hasRight_eq_arity presentation width occurrences member]
    simp only [fanOfDirections, List.length_map, List.length_range]
  · intro group
    rw [fanOfDirections_direction,
      sourceClauseRibbonFanData_direction_eq_indexedRoute presentation width occurrences member]
    by_cases active : literalIndexOfTerminalGroup group < clause.1.literals.length
    · rw [if_pos active]
      have literalMember :
          (clause.1.literals[literalIndexOfTerminalGroup group],
              literalIndexOfTerminalGroup group) ∈ clause.1.literals.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem active)
      have orthogonal := presentation.canonicalOrthogonalRoutes.orthogonal
        clause.1 clause.2 member _ _ literalMember
      simp only [PositionedPeriodicCNF.PlanarIncidencePresentation.canonicalOrthogonalRoutes] at orthogonal
      have rangeLookup : (List.range clause.1.literals.length)[literalIndexOfTerminalGroup group]? =
          some (literalIndexOfTerminalGroup group) := by
        rw [List.getElem?_eq_getElem (by simpa using active), List.getElem_range]
      simpa only [List.getElem?_map, rangeLookup, Option.map_some, Option.getD_some] using
        congrArg AxisDirection.opposite (unitSubdivisionDirections_headD _ orthogonal)
    · rw [if_neg active]
      have rangeLookup : (List.range clause.1.literals.length)[literalIndexOfTerminalGroup group]? =
          none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt active)
      simp only [List.getElem?_map, rangeLookup, Option.map_none, Option.getD_none]

/-- The same semantic fan list indexed just by the ordered clause numbers. -/
theorem clauseIncomingDirectionBlocks_fans_eq_source_range
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3) :
    (clauseIncomingDirectionBlocks source presentation.routes).map fanOfDirections =
      (List.range source.clauses.length).map (sourceClauseRibbonFanData presentation) := by
  rw [clauseIncomingDirectionBlocks_fans_eq_source presentation width occurrences]
  change source.clauses.zipIdx.map (sourceClauseRibbonFanData presentation ∘ Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']

end LeanTrominoes.PeriodicCNFStripReduction
