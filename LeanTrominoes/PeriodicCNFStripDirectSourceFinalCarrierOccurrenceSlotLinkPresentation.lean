/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotStreamSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSemanticSlotBlockFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordFamilyPresentationSymmetry

/-! # Physical-link presentation of direct final carrier occurrence slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierOccurrenceSlotLinkStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierOccurrenceSlotLinkVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private noncomputable def directFinalCarrierOccurrenceSlotLinkDefaultBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  inferInstance

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

private theorem flatten_map_eq_flatMap
    {First Second : Type}
    (values : List First) (block : First → List Second) :
    (values.map block).flatten = values.flatMap block := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      rw [induction]

private def physicalProductOccurrenceSlots
    (equality : DecidableEq (ThreeCNFVariable Nat))
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (links : List (EqualityLink CarrierNode))
    (start : Nat) : List RetainedTerminalSlot :=
  ((links.product [true, false]).zipIdx start).flatMap fun tagged =>
    [@finalCarrierSemanticOccurrenceSlotAt (ThreeCNFVariable Nat) equality
        source tagged.1 tagged.2 0,
      @finalCarrierSemanticOccurrenceSlotAt (ThreeCNFVariable Nat) equality
        source tagged.1 tagged.2 1]

private theorem physicalProduct_eq_semanticOccurrenceSlotsFrom
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    ((links.product [true, false]).zipIdx start).flatMap (fun tagged =>
        [finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 0,
          finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 1]) =
      finalCarrierSemanticOccurrenceSlotsFrom source start links := by
  symm
  exact finalCarrierSemanticOccurrenceSlotsFrom_eq_product
    source links start

set_option maxHeartbeats 400000 in
/-- The compiled direct carrier slot stream is the recursive four-slot
presentation aligned with physical retained links. -/
theorem directSourceFinalCarrierOccurrenceSlots_eq_linkPresentation
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierOccurrenceSlots decider symbols =
      finalCarrierSemanticOccurrenceSlotsFrom
        (directThreeCNFSourceFormula decider symbols)
        (finalCarrierStart
          (directThreeCNFSourceFormula decider symbols))
        (finalCarrierPhysicalLinks
          (directThreeCNFSourceFormula decider symbols)) := by
  rw [directSourceFinalCarrierOccurrenceSlots_eq_semantic,
    directSourceFinalCarrierSemanticOccurrenceSlotBlocks_eq_taggedLinks,
    flatten_map_eq_flatMap,
    directSourceFinalCarrierTaggedLinks_eq_generic]
  unfold finalCarrierTaggedLinks finalCarrierTaggedLinksFrom
  rw [finalCarrierTaggedLinkValues_eq_physicalProduct]
  generalize
    directThreeCNFSourceFormula decider symbols = source
  generalize finalCarrierPhysicalLinks source = links
  generalize finalCarrierStart source = start
  change physicalProductOccurrenceSlots
      directFinalCarrierOccurrenceSlotLinkDefaultBaseDecidableEq
      source links start =
    finalCarrierSemanticOccurrenceSlotsFrom source start links
  calc
    physicalProductOccurrenceSlots
        directFinalCarrierOccurrenceSlotLinkDefaultBaseDecidableEq
        source links start =
      physicalProductOccurrenceSlots
        directSourceFinalStructuralBaseDecidableEq source links start := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq (ThreeCNFVariable Nat) =>
          physicalProductOccurrenceSlots equality source links start)
        directFinalCarrierOccurrenceSlotLinkDefaultBaseDecidableEq
        directSourceFinalStructuralBaseDecidableEq
    _ = finalCarrierSemanticOccurrenceSlotsFrom source start links :=
      physicalProduct_eq_semanticOccurrenceSlotsFrom source links start

end LeanTrominoes.PeriodicCNFStripReduction

end
