/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences

/-! # Source-clause provenance of Figure 9 route pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineSourceTail

/-- Every explicit Figure 9 header/tail pair generated from a positioned
formula comes from one genuine source clause.  The witness retains both the
exact directed clause profile and the clockwise tail row consumed alongside
that clause token. -/
theorem exists_sourceClause_of_mem_sourcePairs_ofFormula
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (pair : Header × List AxisDirection)
    (pairMember : pair ∈
      sourcePairs
        (FormulaShapeDirectionOrdering.ofFormula source routes)
        (source.clauses.zipIdx.map fun taggedClause =>
          orderedTailDirections
            routes taggedClause.2 taggedClause.1)) :
    ∃ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx ∧
      pair.1 ∈ sourceClauseHeaders
        (DirectedClauseProfile.ofClause routes clauseIndex clause) ∧
      pair.2 =
        selectedTailDirections
          (orderedTailDirections routes clauseIndex clause) pair.1 := by
  rw [← sourceOccurrences_map_pair] at pairMember
  rcases List.mem_map.mp pairMember with ⟨occurrence, member, pairEq⟩
  obtain ⟨clause, clauseLookup, profileEq, tailsEq, headerMember⟩ :=
    sourceOccurrences_ofFormula_provenance source routes occurrence member
  refine ⟨clause, occurrence.parentClauseIndex,
    List.mk_mem_zipIdx_iff_getElem?.mpr clauseLookup, ?_, ?_⟩
  · rw [← pairEq]
    simpa only [SourceOccurrence.pair, profileEq] using headerMember
  · rw [← pairEq]
    simp only [SourceOccurrence.pair, tailsEq]

end FormulaShapeFigureNinePolarityRouteTail
end PeriodicCNF
end LeanTrominoes
