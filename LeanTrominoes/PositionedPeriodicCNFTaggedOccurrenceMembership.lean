/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization
import LeanTrominoes.PositionedPeriodicCNFScaling

/-! # Positioned membership behind tagged occurrence indices -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Membership in the erased formula's tagged-literal enumeration recovers
the positioned clause and literal at the two stored indices. -/
theorem exists_members_of_taggedLiterals_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source.erase) :
    ∃ clause : PositionedPeriodicClause Variable,
      ∃ literal : PeriodicLiteral Variable,
        (clause, tagged.2.1) ∈ source.clauses.zipIdx ∧
          (literal, tagged.2.2) ∈ clause.literals.zipIdx := by
  unfold PeriodicThreeSATThree.taggedLiterals
    PositionedPeriodicCNF.erase at member
  rw [List.zipIdx_map] at member
  simp only [List.mem_flatMap, List.mem_map] at member
  rcases member with
    ⟨mappedTaggedClause, mappedTaggedClauseMember,
      taggedLiteral, taggedLiteralMember, taggedEq⟩
  rcases mappedTaggedClauseMember with
    ⟨taggedClause, taggedClauseMember, mappedTaggedClauseEq⟩
  subst mappedTaggedClause
  rcases taggedClause with ⟨clause, clauseIndex⟩
  rcases taggedLiteral with ⟨literal, literalIndex⟩
  simp only [Prod.map, id_eq] at taggedClauseMember taggedLiteralMember taggedEq
  have clauseIndexEq : clauseIndex = tagged.2.1 := by
    simpa using congrArg (fun occurrence => occurrence.2.1) taggedEq
  have literalIndexEq : literalIndex = tagged.2.2 := by
    simpa using congrArg (fun occurrence => occurrence.2.2) taggedEq
  subst clauseIndex
  subst literalIndex
  exact ⟨clause, literal, taggedClauseMember, taggedLiteralMember⟩

/-- Scaling displayed clause positions and then anchor-normalizing preserves
the clause and literal indices of every positioned occurrence. -/
theorem exists_source_members_of_scale_anchorNormalize_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (factor : Nat)
    (placement : PeriodicVariablePlacement Variable)
    {normalizedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (normalizedClauseMember :
      (normalizedClause, clauseIndex) ∈
        ((source.scale factor).anchorNormalize placement).clauses.zipIdx)
    {normalizedLiteral : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (normalizedLiteralMember :
      (normalizedLiteral, literalIndex) ∈
        normalizedClause.literals.zipIdx) :
    ∃ sourceClause : PositionedPeriodicClause Variable,
      ∃ sourceLiteral : PeriodicLiteral Variable,
        (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
          (sourceLiteral, literalIndex) ∈
            sourceClause.literals.zipIdx := by
  unfold PositionedPeriodicCNF.anchorNormalize at normalizedClauseMember
  rw [List.zipIdx_map] at normalizedClauseMember
  rcases List.mem_map.mp normalizedClauseMember with
    ⟨scaledTagged, scaledTaggedMember, normalizedTaggedEq⟩
  rcases scaledTagged with ⟨scaledClause, scaledClauseIndex⟩
  have normalizedClauseEq :
      ({ position := canonicalClausePosition placement scaledClause
         literals := scaledClause.literals.anchorNormalize } :
        PositionedPeriodicClause Variable) = normalizedClause := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.fst normalizedTaggedEq
  have scaledClauseIndexEq : scaledClauseIndex = clauseIndex := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.snd normalizedTaggedEq
  subst normalizedClause
  subst scaledClauseIndex
  rw [PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at scaledTaggedMember
  rcases List.mem_map.mp scaledTaggedMember with
    ⟨sourceTagged, sourceTaggedMember, scaledTaggedEq⟩
  rcases sourceTagged with ⟨sourceClause, sourceClauseIndex⟩
  have scaledClauseEq :
      sourceClause.scale factor = scaledClause := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.fst scaledTaggedEq
  have sourceClauseIndexEq : sourceClauseIndex = clauseIndex := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.snd scaledTaggedEq
  subst scaledClause
  subst sourceClauseIndex
  change
    (normalizedLiteral, literalIndex) ∈
      sourceClause.literals.anchorNormalize.zipIdx at normalizedLiteralMember
  unfold PeriodicClause.anchorNormalize at normalizedLiteralMember
  rw [List.zipIdx_map] at normalizedLiteralMember
  rcases List.mem_map.mp normalizedLiteralMember with
    ⟨⟨sourceLiteral, sourceLiteralIndex⟩, sourceLiteralMember,
      normalizedLiteralEq⟩
  have sourceLiteralIndexEq : sourceLiteralIndex = literalIndex := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.snd normalizedLiteralEq
  subst sourceLiteralIndex
  exact ⟨sourceClause, sourceLiteral,
    sourceTaggedMember, sourceLiteralMember⟩

end PositionedPeriodicCNF
end LeanTrominoes
