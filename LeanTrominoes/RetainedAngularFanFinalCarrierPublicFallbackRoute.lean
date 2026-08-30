/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-! # Public fallback selection for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierPublicFallbackThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- An indexed final carrier rejects the direct atlas and the public
coordinated route is therefore its fallback occurrence route. -/
theorem retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_carrier_eq_fallback
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    {clause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource
          (PeriodicThreeSATThree.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈ clause.literals.zipIdx) :
    let retained := PeriodicThreeSATThree.formula source
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        retained clauseIndex literalIndex =
      retainedFinalFallbackOccurrenceRoute
        retained clause literal clauseIndex literalIndex := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  have retainedLocal : retained.IsLocal :=
    PeriodicThreeSATThree.formula_isLocal sourceLocal
  have retainedWidth : retained.WidthAtMost 3 :=
    PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth
  have retainedOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source
  have retainedClausesNonempty :
      ∀ retainedClause ∈ retained.clauses, retainedClause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty
      source sourceClausesNonempty
  have choiceNone :=
    finalCoordinatedSourceCarrierRouteChoice_eq_none
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed literalIndex
  exact
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      retained retainedLocal retainedWidth retainedOccurrences
      retainedClausesNonempty clauseMember literalMember choiceNone

end PeriodicEightOccurrenceSplit
end LeanTrominoes
