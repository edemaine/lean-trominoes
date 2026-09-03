/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeFixedBlueSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeFixedGreenSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeFixedRedSemantics

/-! # Typed shape of every local grouped variable-incidence block -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- The three local routed offsets select precisely the RGB routed suffixes
inside the typed occurrence's triple-major incidence list. -/
theorem groupedVariableIncidenceLocalBodyBlock_eq_typedShape
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (data : FinalFanOccurrenceData)
    (start : Nat) (routedBody : WireColor → List AxisDirection)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) =
      occurrenceConnectorKind source atom slot)
    (dataKind : data.kind = occurrenceConnectorKind source atom slot) :
    groupedVariableIncidenceLocalBodyBlock start
        (fan, groupedVariableFanGenericSlot slot) data
        (incidenceColors.map routedBody) =
      groupedVariableIncidenceTypedShapeBodies
        source atom slot fan routedBody := by
  cases sourceKind : occurrenceConnectorKind source atom slot with
  | fixedRed =>
      exact groupedVariableIncidenceLocalBodyBlock_eq_typedShape_fixedRed
        source atom slot fan data start routedBody
        (fanKind.trans sourceKind) (dataKind.trans sourceKind) sourceKind
  | fixedGreen =>
      exact groupedVariableIncidenceLocalBodyBlock_eq_typedShape_fixedGreen
        source atom slot fan data start routedBody
        (fanKind.trans sourceKind) (dataKind.trans sourceKind) sourceKind
  | fixedBlue =>
      exact groupedVariableIncidenceLocalBodyBlock_eq_typedShape_fixedBlue
        source atom slot fan data start routedBody
        (fanKind.trans sourceKind) (dataKind.trans sourceKind) sourceKind

end LeanTrominoes.PeriodicCNFStripReduction

end
