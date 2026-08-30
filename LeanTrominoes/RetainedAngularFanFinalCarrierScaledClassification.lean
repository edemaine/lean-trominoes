/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-! # Scaled terminal classification of final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierScaledClassificationThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The scaled final source route at an indexed retained carrier has the
explicit axis-span carrier-lens terminal datum. -/
theorem finalCoordinatedScaledCarrierSourceRoute_classified
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
    (literalIndex : Nat)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              (PeriodicThreeSATThree.formula source)
              clauseIndex literalIndex))) =
      some (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)) := by
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
  have classified :=
    finalCoordinatedScaledSourceRoute_classified
      retained retainedLocal retainedWidth retainedOccurrences
      retainedClausesNonempty clauseMember literalMember
  dsimp only at classified
  change
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes retained
              clauseIndex literalIndex))) =
      some (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (finalCarrierActualTerminalDataAt
          source clauseIndex literalIndex)) at classified
  rw [finalCarrierTerminalData_eq_explicit
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    taggedLink clauseIndex taggedLinkIndexed literalIndex] at classified
  exact classified

end PeriodicEightOccurrenceSplit
end LeanTrominoes
