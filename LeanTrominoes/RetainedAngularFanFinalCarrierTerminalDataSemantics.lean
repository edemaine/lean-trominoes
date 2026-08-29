/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalVectorSemantics

/-! # Actual final terminal data of retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierTerminalThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Actual classified terminal datum at one final carrier incidence. -/
def finalCarrierActualTerminalDataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : RetainedTerminalData :=
  classifiedRetainedTerminalData
    (finalCarrierActualTerminalVectorAt source clauseIndex literalIndex)

/-- Semantic carrier-lens datum at one tagged link and literal index. -/
def finalCarrierSemanticTerminalDataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Nat) : RetainedTerminalData :=
  let retained := PeriodicThreeSATThree.formula source
  carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
    (AxisDirection.axisSpan
      (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
      (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
    (if taggedLink.2 then 0 else 1) literalIndex

/-- Every globally indexed normalized carrier clause uses the exact local
carrier-lens terminal datum of its underlying link and implication. -/
theorem finalCarrierTerminalData_eq
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
    (literalIndex : Nat) :
    finalCarrierActualTerminalDataAt
        source clauseIndex literalIndex =
      finalCarrierSemanticTerminalDataAt
        source taggedLink literalIndex := by
  let retained := PeriodicThreeSATThree.formula source
  have taggedLinkIndexed' := taggedLinkIndexed
  unfold finalCarrierTaggedLinkIndexed at taggedLinkIndexed'
  have taggedLinkMember : taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks retained.incidenceGraph :=
    (List.mem_product.mp
      (List.fst_mem_of_mem_zipIdx taggedLinkIndexed')).1
  unfold finalCarrierActualTerminalDataAt
    finalCarrierSemanticTerminalDataAt
  dsimp only
  calc
    classifiedRetainedTerminalData
          (finalCarrierActualTerminalVectorAt
            source clauseIndex literalIndex) =
        classifiedRetainedTerminalData
          (finalCarrierRawRepresentativeTerminalVectorAt
            source clauseIndex literalIndex) :=
      congrArg classifiedRetainedTerminalData
        (finalCarrierActualTerminalVector_eq_rawRepresentative
          source clauseIndex literalIndex)
    _ =
        classifiedRetainedTerminalData
          (finalCarrierLocalTerminalVectorAt
            source taggedLink literalIndex) :=
      congrArg classifiedRetainedTerminalData
        (finalCarrierRawTerminalVector_eq_local
          source sourceLocal sourceWidth sourceClausesNonempty
            positiveOffsets taggedLink clauseIndex
              taggedLinkIndexed literalIndex)
    _ = _ :=
      carrier_routeTerminalData_eq retained
        (formula_incidenceGraph_isWellFormed source)
        (formula_incidenceGraph_degreeAtMostThree sourceWidth)
        (formula_incidenceGraph_isLocal sourceLocal)
        taggedLink.1 taggedLinkMember
        (if taggedLink.2 then 0 else 1) literalIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
