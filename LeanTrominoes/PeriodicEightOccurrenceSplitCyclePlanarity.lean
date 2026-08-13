/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleDrawing

/-!
# Planarity inside flattened positioned occurrence-splitting cycles

The positioned fixed-eight formula flattens one certified Figure 7
implication ring per source atom.  This module lifts the local continuous
planarity certificate through that flattened indexing:

* every genuine flattened cycle route is simple; and
* two distinct genuine routes belonging to the same source atom avoid one
  another.

Separating different source atoms is intentionally left to the macrocell
geometry of the global construction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open PlanarThreeSAT

/-- Every genuine route in the flattened cycle suffix is simple. -/
theorem allCycleRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (allCycleRoutes source sourcePlacement
        cycleIndex literalIndex) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localClauseMember⟩
  have localSimple :=
    positionedCycleRoute_isSimple
      sourcePlacement metadata.atom localClauseMember
      (clauseEqual ▸ literalMember)
  simpa [allCycleRoutes, metadataLookup] using localSimple

/-- Distinct genuine flattened cycle incidences owned by the same source
atom inherit the complete two-route separation certificate of that atom's
positioned Figure 7 ring. -/
theorem allCycleRoutes_avoidEachOther_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (sameAtom :
      allCycleClauseAtom? source sourcePlacement firstCycleIndex =
        allCycleClauseAtom?
          source sourcePlacement secondCycleIndex)
    (incidencesDistinct :
      firstCycleIndex ≠ secondCycleIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (allCycleRoutes source sourcePlacement
        firstCycleIndex firstLiteralIndex)
      (allCycleRoutes source sourcePlacement
        secondCycleIndex secondLiteralIndex) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement firstClauseMember with
    ⟨firstMetadata, firstMetadataLookup,
      firstClauseEqual, firstLocalClauseMember⟩
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement secondClauseMember with
    ⟨secondMetadata, secondMetadataLookup,
      secondClauseEqual, secondLocalClauseMember⟩
  have atomsEqual :
      firstMetadata.atom = secondMetadata.atom := by
    simpa [allCycleClauseAtom?, firstMetadataLookup,
      secondMetadataLookup] using sameAtom
  have localIncidencesDistinct :
      firstMetadata.localClauseIndex ≠
          secondMetadata.localClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex := by
    rcases incidencesDistinct with
      cycleIndicesDifferent | literalIndicesDifferent
    · left
      intro localIndicesEqual
      apply cycleIndicesDifferent
      apply allCycleClauseMetadata_lookup_key_injective
        source sourcePlacement firstMetadataLookup
          secondMetadataLookup
      exact Prod.ext atomsEqual localIndicesEqual
    · exact Or.inr literalIndicesDifferent
  have secondLocalClauseMember' :
      (secondMetadata.clause,
          secondMetadata.localClauseIndex) ∈
        (cycleClausesFor
          sourcePlacement firstMetadata.atom).zipIdx := by
    simpa [atomsEqual] using secondLocalClauseMember
  have localSeparated :=
    positionedCycleRoutes_avoidEachOther
      sourcePlacement firstMetadata.atom
      firstLocalClauseMember secondLocalClauseMember'
      (firstClauseEqual ▸ firstLiteralMember)
      (secondClauseEqual ▸ secondLiteralMember)
      localIncidencesDistinct
  simpa [allCycleRoutes, firstMetadataLookup,
    secondMetadataLookup, atomsEqual] using localSeparated

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
