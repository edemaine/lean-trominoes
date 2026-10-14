/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup

/-! # Normalized clauses of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierTaggedClauseVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

local instance directFinalCarrierTaggedClauseThreeOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Mapping each tagged link to its normalized implication clause recovers
the indexed direct carrier clause family exactly. -/
theorem directSourceFinalCarrierTaggedClauses_eq
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierClauses decider symbols).zipIdx
        (directSourceFinalCarrierStart decider symbols) =
      (directSourceFinalCarrierTaggedLinks decider symbols).map
        (fun tagged =>
          (normalizedCarrierClauseAt
            (directSourceFinalNormalizedFormula decider symbols) tagged.1,
            tagged.2)) := by
  unfold directSourceFinalCarrierClauses
    directSourceFinalCarrierTaggedLinks
    directSourceFinalNormalizedFormula
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
  rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks,
    List.zipIdx_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
