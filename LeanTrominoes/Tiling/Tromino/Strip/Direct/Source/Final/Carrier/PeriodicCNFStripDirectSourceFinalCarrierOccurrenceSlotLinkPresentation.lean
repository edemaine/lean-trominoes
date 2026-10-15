/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotStreamSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierSemanticSlotBlockFamilySemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Carrier.RetainedAngularFanFinalCarrierLinkRecordFamilyPresentationSymmetry

/-! # Physical-link presentation of direct final carrier occurrence slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierOccurrenceSlotLinkVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

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
    directSourceFinalCarrierTaggedLinks_eq_generic,
    finalCarrierTaggedLinks_eq_physicalPresentation]
  exact product_eq_finalCarrierSemanticOccurrenceSlotsFrom
    (directThreeCNFSourceFormula decider symbols)
    (finalCarrierPhysicalLinks (directThreeCNFSourceFormula decider symbols))
    (finalCarrierStart (directThreeCNFSourceFormula decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
