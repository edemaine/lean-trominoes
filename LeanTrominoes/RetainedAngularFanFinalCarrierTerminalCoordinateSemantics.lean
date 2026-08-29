/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalDataSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinate
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateData

/-! # Actual final terminal coordinates of retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- At a globally indexed final carrier incidence, the terminal coordinate
is the coordinate of the corresponding tagged carrier-lens datum. -/
theorem finalCarrierOccurrenceTerminalCoordinate_eq
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
    (atom : WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
    (literalIndex : Nat) :
    ofLex (retainedOccurrenceTerminalCoordinate
        (finalCoordinatedSourceRoutes
          (PeriodicThreeSATThree.formula source))
        (atom, clauseIndex, literalIndex)) =
      retainedTerminalDataCoordinate
        (carrierLensRouteTerminalDataTagged
          taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
          taggedLink.2 literalIndex) := by
  let retained := PeriodicThreeSATThree.formula source
  have taggedLinkIndexed' := taggedLinkIndexed
  unfold finalCarrierTaggedLinkIndexed at taggedLinkIndexed'
  have taggedLinkMember : taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks retained.incidenceGraph :=
    (List.mem_product.mp
      (List.fst_mem_of_mem_zipIdx taggedLinkIndexed')).1
  change retainedTerminalDataCoordinate
      (finalCarrierActualTerminalDataAt
        source clauseIndex literalIndex) = _
  unfold carrierLensRouteTerminalDataTagged
  calc
    retainedTerminalDataCoordinate
          (finalCarrierActualTerminalDataAt
            source clauseIndex literalIndex) =
        retainedTerminalDataCoordinate
          (classifiedRetainedTerminalData
            (finalCarrierRawRepresentativeTerminalVectorAt
              source clauseIndex literalIndex)) :=
      congrArg retainedTerminalDataCoordinate
        (congrArg classifiedRetainedTerminalData
          (finalCarrierActualTerminalVector_eq_rawRepresentative
            source clauseIndex literalIndex))
    _ = retainedTerminalDataCoordinate
          (classifiedRetainedTerminalData
            (finalCarrierLocalTerminalVectorAt
              source taggedLink literalIndex)) :=
      congrArg retainedTerminalDataCoordinate
        (congrArg classifiedRetainedTerminalData
          (finalCarrierRawTerminalVector_eq_local
            source sourceLocal sourceWidth sourceClausesNonempty
              positiveOffsets taggedLink clauseIndex
                taggedLinkIndexed literalIndex))
    _ = _ :=
      congrArg retainedTerminalDataCoordinate
        (carrier_routeTerminalData_eq retained
          (formula_incidenceGraph_isWellFormed source)
          (formula_incidenceGraph_degreeAtMostThree sourceWidth)
          (formula_incidenceGraph_isLocal sourceLocal)
          taggedLink.1 taggedLinkMember
          (if taggedLink.2 then 0 else 1) literalIndex)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
