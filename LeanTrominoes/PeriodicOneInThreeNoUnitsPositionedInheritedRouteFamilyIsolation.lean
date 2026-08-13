/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedSuffixIsolation

/-!
# Endpoint isolation for inherited unit-elimination suffix families

This module lifts the per-route connector theorem through the proof-backed
inherited-incidence selector.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Pointwise endpoint isolation and the vertical one-segment exception lift
to final-endpoint isolation of every inherited unit-elimination suffix. -/
theorem inheritedRouteSuffixesRoutes_lastNotInDropLast
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceIsolation :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          AxisDirection.HeadNotInTail
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)) ∧
            AxisDirection.LastNotInDropLast
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)))
    (sourceVerticalIfLastIsExit :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit →
            PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral = exit →
            exit.1 =
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffixesRoutes
          source sourcePlacement sourceRoutes
          clauseIndex literalIndex)) := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have endpoints :=
    sourceEndpoints data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember data.sourceLiteral
      data.sourceLiteralIndex data.sourceLiteralMember
  rcases sourceExits data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember data.sourceLiteral
      data.sourceLiteralIndex data.sourceLiteralMember with
    ⟨sourceExit, sourceTailHead⟩
  have sourceLiteralIndexLt : data.sourceLiteralIndex < 3 := by
    have sourceLiteralIndexBound :=
      (List.mem_zipIdx' data.sourceLiteralMember).1
    have sourceClauseMember : data.sourceClause ∈ source.clauses :=
      List.fst_mem_of_mem_zipIdx data.sourceClauseMember
    have sourceClauseWidth : data.sourceClause.literals.length ≤ 3 := by
      apply sourceWidth data.sourceClause.literals
      exact List.mem_map.mpr
        ⟨data.sourceClause, sourceClauseMember, rfl⟩
    omega
  have isolated :=
    inheritedRouteSuffix_lastNotInDropLast
      (placement source sourcePlacement) sourcePlacement
      data.sourceClause data.generatedClause data.sourceLiteralIndex
      sourceLiteralIndexLt
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      sourceExit
      (PositionedPeriodicCNF.canonicalLiteralPosition
        sourcePlacement data.sourceClause data.sourceLiteral)
      endpoints.1 sourceTailHead endpoints.2
      (sourceOrthogonal data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember data.sourceLiteral
        data.sourceLiteralIndex data.sourceLiteralMember)
      (sourceIsolation data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember data.sourceLiteral
        data.sourceLiteralIndex data.sourceLiteralMember)
      (fun finalEqual =>
        sourceVerticalIfLastIsExit
          data.sourceClause data.sourceClauseIndex
          data.sourceClauseMember data.sourceLiteral
          data.sourceLiteralIndex data.sourceLiteralMember
          sourceExit sourceTailHead finalEqual)
  simpa [inheritedRouteSuffixesRoutes, dataLookup] using isolated

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
