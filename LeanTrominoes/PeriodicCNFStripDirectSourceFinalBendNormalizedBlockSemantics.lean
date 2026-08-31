/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendSemanticSlotPresentation
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Semantic normal form of direct final-bend record blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendNormalizedBlockVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

private theorem flatten_map_eq_flatMap
    {First Second : Type}
    (values : List First) (block : First → List Second) :
    (values.map block).flatten = values.flatMap block := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      rw [induction]

private theorem directSourceFinalBendOccurrenceSlots_eq_presentation
    (symbols : List encoding.Γ) :
    directSourceFinalBendOccurrenceSlots decider symbols =
      finalBendSemanticOccurrenceSlotsFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)) := by
  rw [directSourceFinalBendOccurrenceSlots_eq_semantic,
    directSourceFinalBendSemanticOccurrenceSlotBlocks_eq_tagged]
  unfold directSourceFinalBendTaggedSemanticOccurrenceSlotBlocks
    directSourceFinalBendIndexedTaggedBends
    finalBendNamedSemanticOccurrenceSlotBlocksAt
  rw [flatten_map_eq_flatMap,
    finalBendSemanticOccurrenceSlotsFrom_eq_product]

private theorem directSourceFinalBendFallbackRecordGeometries_eq_base
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackRecordGeometries decider symbols =
      (baseRouteBends
        (directSourceFinalNormalizedFormula decider symbols)).map
          fun routeBend =>
            ({ firstPort := routeBend.incomingPort
               secondPort := routeBend.outgoingPort } :
              BendFallbackRouteTailRecords.Geometry) := by
  unfold directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries
    baseRouteBends
  rw [directSourceFormula_eq_finalNormalized]
  rw [List.map_flatMap]
  generalize
    directSourceFinalNormalizedFormula decider symbols = formula
  exact decidableEq_application_irrel
    (fun equality : DecidableEq Variable =>
      (@PeriodicCNF.numericRouteDescriptors Variable equality formula).flatMap
        fun descriptor =>
          (routeBends descriptor.edgeIndex (0, 0)
            descriptor.route).map fun routeBend =>
              ({ firstPort := routeBend.incomingPort
                 secondPort := routeBend.outgoingPort } :
                BendFallbackRouteTailRecords.Geometry))
    directSourceVariableDecidableEq
    directSourceFinalOriginalVariableDecidableEq

/-- The declarative normalized direct bend blocks are exactly the generic
semantic block normal form over untranslated physical bends. -/
theorem directSourceFinalBendNormalizedFallbackRecordBlocks_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackRecordBlocks decider symbols =
      finalBendNormalizedRecordBlocksFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)) := by
  unfold directSourceFinalBendNormalizedFallbackRecordBlocks
  rw [directSourceFinalBendFallbackRecordGeometries_eq_base,
    directSourceFinalBendOccurrenceSlots_eq_presentation]
  exact (finalBendNormalizedRecordBlocksFrom_eq_blocks
    (directSourceFinalNormalizedFormula decider symbols)
    (baseRouteBends
      (directSourceFinalNormalizedFormula decider symbols))
    (directSourceFinalBendStart decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
