/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeData

/-! # Fixed-red local grouped variable-incidence shape -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Local body lookup has the typed triple/RGB shape for a fixed-red
occurrence. -/
theorem groupedVariableIncidenceLocalBodyBlock_eq_typedShape_fixedRed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (data : FinalFanOccurrenceData)
    (start : Nat) (routedBody : WireColor → List AxisDirection)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) =
      .fixedRed)
    (dataKind : data.kind = .fixedRed)
    (sourceKind : occurrenceConnectorKind source atom slot =
      .fixedRed) :
    groupedVariableIncidenceLocalBodyBlock start
        (fan, groupedVariableFanGenericSlot slot) data
        (incidenceColors.map routedBody) =
      groupedVariableIncidenceTypedShapeBodies
        source atom slot fan routedBody := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  change kind = .fixedRed at dataKind
  subst kind
  simp (disch := omega) [fanKind, sourceKind,
    groupedVariableIncidenceLocalBodyBlock,
    groupedVariableIncidenceTypedShapeBodies,
    groupedVariableIncidencePrefixQueryBlock,
    groupedVariableIncidenceTriples,
    groupedVariableFanSiteSlot_genericSlot,
    GroupedRoutedIncidenceKeyLocality.keyBlock,
    directFinalOccurrenceRoutedIncidenceKeyOffsets,
    occurrenceTriples, routedOccurrenceTriple, variableSiteTripleOfTyped,
    allFixedRedTriples, incidenceColors,
    FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.mul_comm]

end LeanTrominoes.PeriodicCNFStripReduction

end
