/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordFamilyPresentation

/-! # Reverse orientations of final carrier family presentations -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PlanarThreeSAT

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Physical carrier links with the equality implementation used by the
generic tagged-link presentation. -/
def finalCarrierPhysicalLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (EqualityLink CarrierNode) :=
  letI : DecidableEq (ThreeOccurrenceVariable Variable) :=
    PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
  retainedDrawingCompleteCarrierLinks
    (PeriodicThreeSATThree.formula source).incidenceGraph

/-- The tagged-link values are the Boolean product of the named physical
carrier links. -/
theorem finalCarrierTaggedLinkValues_eq_physicalProduct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    finalCarrierTaggedLinkValues source =
      (finalCarrierPhysicalLinks source).product [true, false] := by
  unfold finalCarrierTaggedLinkValues finalCarrierPhysicalLinks
  rfl

/-- Clause-major tagged-link slots flatten to the recursive physical-link
slot presentation. -/
theorem product_eq_finalCarrierSemanticOccurrenceSlotsFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    ((links.product [true, false]).zipIdx start).flatMap (fun tagged =>
        [finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 0,
          finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 1]) =
      finalCarrierSemanticOccurrenceSlotsFrom source start links :=
  (finalCarrierSemanticOccurrenceSlotsFrom_eq_product
    source links start).symm

/-- The normalized carrier block zipper is the recursive physical-link block
presentation. -/
theorem blocks_eq_finalCarrierNormalizedRecordBlocksFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    CarrierNormalizedFallbackRouteTailRecords.blocks
        (links.map (CarrierFallbackRouteTailRecords.Geometry.ofLink
          (PeriodicThreeSATThree.formula source)))
        (finalCarrierSemanticOccurrenceSlotsFrom source start links) =
      finalCarrierNormalizedRecordBlocksFrom source start links :=
  (finalCarrierNormalizedRecordBlocksFrom_eq_blocks
    source links start).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
