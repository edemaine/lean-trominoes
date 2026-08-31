/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordGeometrySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotLinkPresentation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRouteTailRecordData
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordFamilyPresentationSymmetry

/-! # Semantic normal form of direct final-carrier record blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierNormalizedBlockVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

private theorem directSourceFormula_eq_genericFinal
    (symbols : List encoding.Γ) :
    directSourceFormula decider symbols =
      PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols) := by
  calc
    directSourceFormula decider symbols =
        directSourceFinalNormalizedFormula decider symbols :=
      directSourceFormula_eq_finalNormalized decider symbols
    _ = PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols) := by
      unfold directSourceFinalNormalizedFormula
      exact decidableEq_application_irrel
        (fun equality : DecidableEq (ThreeCNFVariable Nat) =>
          @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat) equality
            (directThreeCNFSourceFormula decider symbols))
        directSourceFinalOriginalBaseDecidableEq
        directSourceFinalStructuralBaseDecidableEq

private def directFinalCarrierGeometriesAt
    (equality : DecidableEq Variable)
    (source : PeriodicCNF (ThreeCNFVariable Nat)) :
    List CarrierFallbackRouteTailRecords.Geometry :=
  letI : DecidableEq Variable := equality
  let formula := @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
    directSourceFinalStructuralBaseDecidableEq source
  (retainedDrawingCompleteCarrierLinks formula.incidenceGraph).map
    (CarrierFallbackRouteTailRecords.Geometry.ofLink formula)

private theorem structuralCarrierGeometries_eq_physicalMap
    (source : PeriodicCNF (ThreeCNFVariable Nat)) :
    directFinalCarrierGeometriesAt
        directSourceFinalStructuralVariableDecidableEq source =
      (finalCarrierPhysicalLinks source).map
        (@CarrierFallbackRouteTailRecords.Geometry.ofLink Variable
          directSourceFinalStructuralVariableDecidableEq
          (@PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
            directSourceFinalStructuralBaseDecidableEq source)) := by
  rfl

private theorem structuralCarrierBlocksFrom_eq_semantic
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    CarrierNormalizedFallbackRouteTailRecords.blocks
        (links.map (@CarrierFallbackRouteTailRecords.Geometry.ofLink Variable
          directSourceFinalStructuralVariableDecidableEq
          (@PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
            directSourceFinalStructuralBaseDecidableEq source)))
        (finalCarrierSemanticOccurrenceSlotsFrom source start links) =
      finalCarrierNormalizedRecordBlocksFrom source start links := by
  induction links generalizing start with
  | nil =>
      simp only [List.map_nil, finalCarrierSemanticOccurrenceSlotsFrom,
        CarrierNormalizedFallbackRouteTailRecords.blocks,
        finalCarrierNormalizedRecordBlocksFrom]
  | cons link links induction =>
      simp only [finalCarrierNormalizedRecordBlocksFrom,
        finalCarrierSemanticOccurrenceSlotsFrom, List.map_cons,
        List.cons_append, List.nil_append,
        CarrierNormalizedFallbackRouteTailRecords.blocks,
        finalCarrierNormalizedRecordBlockAt]
      rw [induction (start + 2)]
      rfl

/-- The declarative normalized direct carrier blocks are exactly the generic
semantic block normal form over physical links. -/
theorem directSourceFinalCarrierNormalizedFallbackRecordBlocks_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackRecordBlocks decider symbols =
      finalCarrierNormalizedRecordBlocksFrom
        (directThreeCNFSourceFormula decider symbols)
        (finalCarrierStart
          (directThreeCNFSourceFormula decider symbols))
        (finalCarrierPhysicalLinks
          (directThreeCNFSourceFormula decider symbols)) := by
  unfold directSourceFinalCarrierNormalizedFallbackRecordBlocks
  rw [directSourceFinalCarrierFallbackRecordGeometries_eq_links,
    directSourceFinalCarrierOccurrenceSlots_eq_linkPresentation,
    directSourceFormula_eq_genericFinal]
  generalize
    directThreeCNFSourceFormula decider symbols = source
  change CarrierNormalizedFallbackRouteTailRecords.blocks
      (directFinalCarrierGeometriesAt
        directFinalCarrierGeometrySemanticsVariableDecidableEq source)
      (finalCarrierSemanticOccurrenceSlotsFrom source
        (finalCarrierStart source) (finalCarrierPhysicalLinks source)) =
    finalCarrierNormalizedRecordBlocksFrom source
      (finalCarrierStart source) (finalCarrierPhysicalLinks source)
  calc
    CarrierNormalizedFallbackRouteTailRecords.blocks
        (directFinalCarrierGeometriesAt
          directFinalCarrierGeometrySemanticsVariableDecidableEq source)
        (finalCarrierSemanticOccurrenceSlotsFrom source
          (finalCarrierStart source) (finalCarrierPhysicalLinks source)) =
      CarrierNormalizedFallbackRouteTailRecords.blocks
        (directFinalCarrierGeometriesAt
          directSourceFinalStructuralVariableDecidableEq source)
        (finalCarrierSemanticOccurrenceSlotsFrom source
          (finalCarrierStart source) (finalCarrierPhysicalLinks source)) := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          CarrierNormalizedFallbackRouteTailRecords.blocks
            (directFinalCarrierGeometriesAt equality source)
            (finalCarrierSemanticOccurrenceSlotsFrom source
              (finalCarrierStart source) (finalCarrierPhysicalLinks source)))
        directFinalCarrierGeometrySemanticsVariableDecidableEq
        directSourceFinalStructuralVariableDecidableEq
    _ = finalCarrierNormalizedRecordBlocksFrom source
        (finalCarrierStart source) (finalCarrierPhysicalLinks source) :=
      by
        rw [structuralCarrierGeometries_eq_physicalMap]
        generalize finalCarrierPhysicalLinks source = links
        generalize finalCarrierStart source = start
        exact structuralCarrierBlocksFrom_eq_semantic source
          links start

end LeanTrominoes.PeriodicCNFStripReduction

end
