/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierGeometrySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRetainedIncidencesNonempty

/-! # Semantic links of direct-source carrier record geometries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open CarrierFallbackRouteTailRecords

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierGeometrySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierGeometrySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct normalized fallback record geometries are exactly the retained
carrier-link geometries of the direct final source, in presentation order. -/
theorem directSourceFinalCarrierFallbackRecordGeometries_eq_links
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackRecordGeometries decider symbols =
      (retainedDrawingCompleteCarrierLinks
        (directSourceFormula decider symbols).incidenceGraph).map
          (Geometry.ofLink (directSourceFormula decider symbols)) := by
  unfold directSourceFinalCarrierFallbackRecordGeometries
    directSourceFinalCarrierFallbackEntries
  simpa only [routeDescriptorCarrierRankDatumsAtPeriod] using
    numericCarrierGeometries_eq_links
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSource_incidencesWithMetadata_ne_nil decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
