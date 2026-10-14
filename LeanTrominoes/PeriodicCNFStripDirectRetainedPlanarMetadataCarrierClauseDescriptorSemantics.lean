/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Correctness of direct retained carrier descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedCarrierSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directRetainedClauseFamilyDataVariableDecidableEq

/-- The rank-ordered route-descriptor compiler emits exactly the retained
carrier descriptor family of the direct geometric source. -/
theorem directRetainedPlanarMetadataCarrierClauseDescriptors_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols =
      directRetainedPlanarMetadataCompiledCarrierClauseDescriptors
        decider symbols := by
  unfold directRetainedPlanarMetadataCarrierClauseDescriptors
    directRetainedPlanarMetadataCompiledCarrierClauseDescriptors
  symm
  apply
    FormulaShapeRetainedPlanarMetadataDirection.rankOrderedCarrierLinkDescriptorScan_eq_carrierMetadataClauseDescriptors
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  · unfold directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  · exact directSourceFormula_isForwardLocal decider symbols
  · exact directSource_incidencesWithMetadata_ne_nil decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
