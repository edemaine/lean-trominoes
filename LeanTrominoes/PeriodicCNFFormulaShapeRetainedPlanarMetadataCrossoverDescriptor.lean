/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverLiteralProfiles
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverRouteDirection

/-! # Descriptors of retained crossover metadata clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The complete finite descriptor of every retained physical crossover
clause is exactly the corresponding fixed Figure 8(b) descriptor. -/
theorem metadataClauseDescriptor_crossoverClauseAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossingHalo source.incidenceGraph)
    (clause : EmbeddedClause CrossoverVariable)
    (localClauseIndex : Nat) :
    metadataClauseDescriptor source
        ⟨crossoverClauseAt crossing clause,
          .crossover crossing localClauseIndex⟩ =
      .clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          crossoverStraightIncidenceDrawing.routes localClauseIndex
          ⟨(0, 0),
            FormulaShapeCrossoverDirection.zeroOffsetClause clause⟩) := by
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
    DrawingPlanarSATClauseSource.localClauseIndex
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  rw [normalizedClause_crossoverClauseAt_eq
    source wellFormed degree isLocal crossing crossingMember
    clause localClauseIndex]
  unfold FormulaShapeCrossoverDirection.wrappedNormalizedClause
    FormulaShapeCrossoverDirection.zeroOffsetClause
  rw [List.zipIdx_map, List.zipIdx_map]
  simp only [List.map_map]
  apply List.map_congr_left
  intro taggedLiteral _taggedLiteralMember
  apply Prod.ext
  · rcases taggedLiteral with ⟨⟨role, value⟩, literalIndex⟩
    simp [FormulaShapeDirectionOrdering.literalProfile]
  · exact crossover_routeFirstDirection_eq
      source crossing localClauseIndex taggedLiteral.2

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
