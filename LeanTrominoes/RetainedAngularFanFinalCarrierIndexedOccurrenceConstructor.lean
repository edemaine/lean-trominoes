/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Constructing indexed final retained-carrier occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- A tagged retained carrier and one literal of its normalized implication
clause determine the corresponding positioned final occurrence. -/
noncomputable def FinalCarrierIndexedOccurrence.ofTaggedLinkLiteral
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨ incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈
        (normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula source) taggedLink).zipIdx) :
    FinalCarrierIndexedOccurrence Variable := by
  let retained := PeriodicThreeSATThree.formula source
  let normalizedClause := normalizedCarrierClauseAt retained taggedLink
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    taggedLink clauseIndex taggedLinkIndexed
  have mappedLookup :
      ((finalCoordinatedSource retained).clauses.map
          PositionedPeriodicClause.literals)[clauseIndex]? =
        some normalizedClause := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact lookups.1
  rw [List.getElem?_map] at mappedLookup
  generalize positionedLookup :
      (finalCoordinatedSource retained).clauses[clauseIndex]? =
        positionedOption at mappedLookup
  cases positionedOption with
  | none => simp at mappedLookup
  | some positionedClause =>
      simp only [Option.map_some, Option.some.injEq] at mappedLookup
      refine
        { source := source
          sourceLocal := sourceLocal
          sourceWidth := sourceWidth
          sourceClausesNonempty := sourceClausesNonempty
          positiveOffsets := positiveOffsets
          taggedLink := taggedLink
          clauseIndex := clauseIndex
          taggedLinkIndexed := taggedLinkIndexed
          clause := positionedClause
          clauseMember := (List.mem_zipIdx_iff_getElem?).mpr positionedLookup
          literal := literal
          literalIndex := literalIndex
          literalMember := ?_ }
      rw [mappedLookup]
      simpa only [retained, normalizedClause] using literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
