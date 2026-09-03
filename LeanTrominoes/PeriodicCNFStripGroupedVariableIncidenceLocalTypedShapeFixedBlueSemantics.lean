/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeData

/-! # Fixed-blue local grouped variable-incidence shape -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Local body lookup has the typed triple/RGB shape for a fixed-blue
occurrence. -/
theorem groupedVariableIncidenceLocalBodyBlock_eq_typedShape_fixedBlue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (data : FinalFanOccurrenceData)
    (start : Nat) (routedBody : WireColor → List AxisDirection)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) =
      .fixedBlue)
    (dataKind : data.kind = .fixedBlue)
    (sourceKind : occurrenceConnectorKind source atom slot =
      .fixedBlue) :
    groupedVariableIncidenceLocalBodyBlock start
        (fan, groupedVariableFanGenericSlot slot) data
        (incidenceColors.map routedBody) =
      groupedVariableIncidenceTypedShapeBodies
        source atom slot fan routedBody := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  change kind = .fixedBlue at dataKind
  subst kind
  have indexTwo : 1 + (1 + start * 3) = 2 + start * 3 := by omega
  have indexSix' :
      1 + (1 + (1 + (1 + (2 + start * 3)))) =
        start * 3 + 6 := by omega
  have indexSeven'' : 1 + (start * 3 + 6) = start * 3 + 7 := by omega
  simp (disch := omega) [fanKind, sourceKind,
    groupedVariableIncidenceLocalBodyBlock,
    groupedVariableIncidenceTypedShapeBodies,
    groupedVariableIncidencePrefixQueryBlock,
    groupedVariableIncidenceTriples,
    groupedVariableFanSiteSlot_genericSlot,
    GroupedRoutedIncidenceKeyLocality.keyBlock,
    directFinalOccurrenceRoutedIncidenceKeyOffsets,
    occurrenceTriples, routedOccurrenceTriple, variableSiteTripleOfTyped,
    allOrdinaryTriples, incidenceColors,
    FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody,
    indexTwo, indexSix', indexSeven'',
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.mul_comm, Nat.add_comm]

end LeanTrominoes.PeriodicCNFStripReduction

end
