/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceSourceRouteData

/-! # Correctness of proof-free occurrence source-route rebasing -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PeriodicOrthocrossing

/-- On every active occurrence, proof-free lookup selects the same incidence
as the semantic choice-backed ribbon construction. -/
theorem occurrenceSourceRouteFromData_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    occurrenceSourceRouteFromData source placement presentation.routes entry.1 =
      occurrenceSourceRoute presentation entry := by
  let data := occurrenceSpliceData presentation entry
  have clauseIndexLt :
      data.indexed.1.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx data.clauseMember
  have clauseAt :
      source.clauses[data.indexed.1.clauseIndex] =
        data.positionedClause :=
    (List.mem_zipIdx' data.clauseMember).2.symm
  have clauseLiteralsAt :
      (((source.clauses[data.indexed.1.clauseIndex]?).map
        PositionedPeriodicClause.literals).getD []) =
          data.positionedClause.literals := by
    rw [List.getElem?_eq_getElem clauseIndexLt, clauseAt]
    rfl
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      source data.indexedMember with
    ⟨indexedPositionedClause, indexedLiteral,
      indexedClauseMember, indexedLiteralMember, indexedEq⟩
  have indexedClauseAt :
      source.clauses[data.indexed.1.clauseIndex] =
        indexedPositionedClause :=
    (List.mem_zipIdx' indexedClauseMember).2.symm
  have indexedPositionedClauseEq :
      indexedPositionedClause = data.positionedClause :=
    indexedClauseAt.symm.trans clauseAt
  have indexedClauseEq :
      data.indexed.1.clause = data.positionedClause.literals := by
    have fields := congrArg
      (fun incidence : CNFIncidence Variable => incidence.clause) indexedEq
    simpa [indexedPositionedClauseEq] using fields
  unfold occurrenceSourceRouteFromData
  rw [data.occurrenceLookup]
  rw [← data.metadataEq]
  unfold occurrenceSourceRoute
    PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute
  change
    translatePolyline
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor
              (((source.clauses[data.indexed.1.clauseIndex]?).map
                PositionedPeriodicClause.literals).getD []))
            data.indexed.1.literal.offset))
        (presentation.routes data.indexed.1.clauseIndex
          data.indexed.1.literalIndex).reverse =
      translatePolyline
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor data.indexed.1.clause)
            data.indexed.1.literal.offset))
        (presentation.routes data.indexed.1.clauseIndex
          data.indexed.1.literalIndex).reverse
  rw [clauseLiteralsAt]
  rw [indexedClauseEq]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
