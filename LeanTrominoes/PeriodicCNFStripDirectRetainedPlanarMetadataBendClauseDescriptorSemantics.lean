/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Correctness of direct retained bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBendSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedBendSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directRetainedClauseFamilyDataVariableDecidableEq

/-- The affine route-pair scan emits exactly the retained bend descriptor
family of the direct geometric source. -/
theorem directRetainedPlanarMetadataBendClauseDescriptors_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataBendClauseDescriptors decider symbols =
      directRetainedPlanarMetadataCompiledBendClauseDescriptors
        decider symbols := by
  unfold directRetainedPlanarMetadataCompiledBendClauseDescriptors
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  symm
  apply
    PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBendDescriptorStream_eq_bendMetadataClauseDescriptors
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  · unfold directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  · exact directSourceFormula_isForwardLocal decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
