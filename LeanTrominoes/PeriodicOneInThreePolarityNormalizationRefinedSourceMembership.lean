/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertexBounds

/-! # Source membership behind polarity refinement -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Anchor normalization and threefold source scaling preserve both
presentation indices of every positioned literal occurrence. -/
theorem exists_source_members_of_refinedSource_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {refinedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (refinedClauseMember :
      (refinedClause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {refinedLiteral : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (refinedLiteralMember :
      (refinedLiteral, literalIndex) ∈ refinedClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
        (sourceLiteral, literalIndex) ∈
          sourceClause.literals.zipIdx := by
  unfold refinedSource at refinedClauseMember
  rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map] at refinedClauseMember
  rcases List.mem_map.mp refinedClauseMember with
    ⟨normalizedTagged, normalizedTaggedMember, refinedTaggedEq⟩
  rcases normalizedTagged with ⟨normalizedClause, normalizedIndex⟩
  have refinedClauseEq :
      normalizedClause.scale refinementFactor = refinedClause := by
    simpa only [Prod.map, id_eq] using congrArg Prod.fst refinedTaggedEq
  have normalizedIndexEq : normalizedIndex = clauseIndex := by
    simpa only [Prod.map, id_eq] using congrArg Prod.snd refinedTaggedEq
  subst refinedClause
  subst normalizedIndex
  rw [PositionedPeriodicCNF.anchorNormalize, List.zipIdx_map] at normalizedTaggedMember
  rcases List.mem_map.mp normalizedTaggedMember with
    ⟨sourceTagged, sourceTaggedMember, normalizedTaggedEq⟩
  rcases sourceTagged with ⟨sourceClause, sourceIndex⟩
  have normalizedClauseEq :
      ({ position :=
          PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause
         literals := sourceClause.literals.anchorNormalize } :
        PositionedPeriodicClause Variable) = normalizedClause := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.fst normalizedTaggedEq
  have sourceIndexEq : sourceIndex = clauseIndex := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.snd normalizedTaggedEq
  subst normalizedClause
  subst sourceIndex
  change
    (refinedLiteral, literalIndex) ∈
      sourceClause.literals.anchorNormalize.zipIdx at refinedLiteralMember
  unfold PeriodicClause.anchorNormalize at refinedLiteralMember
  rw [List.zipIdx_map] at refinedLiteralMember
  rcases List.mem_map.mp refinedLiteralMember with
    ⟨⟨sourceLiteral, sourceLiteralIndex⟩, sourceTaggedLiteralMember,
      refinedTaggedLiteralEq⟩
  have sourceLiteralIndexEq :
      sourceLiteralIndex = literalIndex := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.snd refinedTaggedLiteralEq
  subst sourceLiteralIndex
  exact ⟨sourceClause, sourceLiteral,
    sourceTaggedMember, sourceTaggedLiteralMember⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
