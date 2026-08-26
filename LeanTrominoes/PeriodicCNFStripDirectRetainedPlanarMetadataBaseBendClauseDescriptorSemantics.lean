/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBaseBendScanSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Semantics of direct untranslated retained-bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBaseBendSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedBaseBendSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct base scan is one canonical descriptor block for every bend
identity, with its translated physical copies removed. -/
theorem directRetainedPlanarMetadataBaseBendClauseDescriptors_eq_semantic
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            canonicalBendDescriptorBlock
              routeBend.incomingPort routeBend.outgoingPort false := by
  unfold directRetainedPlanarMetadataBaseBendClauseDescriptors
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  apply RouteDescriptorPairAffine.affineBaseBendDescriptorStream_numericRouteDescriptors
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  · unfold directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  · exact directSourceFormula_isForwardLocal decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
