/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseGadgetOriginCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionBlocks

/-! # Clause-origin coordinates retain actual clause and triple indices -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

private theorem clausePosition_of_member {Variable : Type} (source : PositionedPeriodicCNF Variable)
    (clause : PositionedPeriodicClause Variable) (index : Nat)
    (member : (clause, index) ∈ source.clauses.zipIdx) : source.clausePosition index = clause.position := by
  rw [PositionedPeriodicCNF.clausePosition, List.mk_mem_zipIdx_iff_getElem?.mp member]
  rfl

/-- The geometric origin list is the actual clause-indexed origin lookup,
with each source presentation index retained. -/
theorem horizontalClauseGadgetOrigins_eq_indexed (source : PeriodicCNF Nat) :
    horizontalClauseGadgetOrigins source =
      (horizontalNormalizedRoutedFormulaComputed source).clauses.zipIdx.map
        (fun clause => horizontalThreeDMClauseOriginComputed source clause.2) := by
  let clauses := (horizontalNormalizedRoutedFormulaComputed source).clauses
  have mapped := congrArg (List.map fun clause : PositionedPeriodicClause RoutedVariable =>
    Cell.add (Cell.scale 128 clause.position) (50, 60)) (List.zipIdx_map_fst 0 clauses)
  rw [List.map_map] at mapped
  refine mapped.symm.trans ?_
  apply List.map_congr_left
  intro tagged member
  unfold horizontalThreeDMClauseOriginComputed horizontalNormalizedRoutedClausePositionComputed
  rw [clausePosition_of_member _ tagged.1 tagged.2 member]
  rfl

/-- Expanding the nine local clause positions gives exactly the established
clause-triple suffix, with no permutation or coordinate deduplication. -/
theorem horizontalClauseGadgetOrigins_clauseTriplePositions (source : PeriodicCNF Nat) :
    (horizontalClauseGadgetOrigins source).flatMap
      (fun origin => (allClauseSets.map X3CClauseOrthogonal.setPosition).map (Cell.add origin)) =
      horizontalThreeDMClauseTriplePositionsComputed source := by
  rw [horizontalClauseGadgetOrigins_eq_indexed]
  simp only [List.flatMap_map, List.map_map, Function.comp_def,
    horizontalThreeDMClauseTriplePositionsComputed, PositionedPeriodicCNF.erase,
    List.zipIdx_map, Prod.map, id_eq]

end LeanTrominoes.PeriodicCNFStripReduction
end
