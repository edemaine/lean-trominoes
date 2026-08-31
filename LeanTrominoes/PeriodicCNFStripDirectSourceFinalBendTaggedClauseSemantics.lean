/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors

/-! # Tagged-bend presentation of direct final bend clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendTaggedClauseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendTaggedClauseVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

local instance directFinalBendTaggedClauseThreeOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Mapping each tagged untranslated bend to its normalized implication
recovers the indexed direct bend family exactly. -/
theorem directSourceFinalBendTaggedClauses_eq
    (symbols : List encoding.Γ) :
    (directSourceFinalBendClauses decider symbols).zipIdx
        (directSourceFinalBendStart decider symbols) =
      (((baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)).product
        [true, false]).zipIdx
          (directSourceFinalBendStart decider symbols)).map
        (fun tagged =>
          (normalizedBendClauseAt
            (directSourceFinalNormalizedFormula decider symbols) tagged.1,
            tagged.2)) := by
  unfold directSourceFinalBendClauses
    directSourceFinalNormalizedFormula
    PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
  rw [baseBendNormalizedClauses_eq_map_baseTaggedBends,
    List.zipIdx_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
