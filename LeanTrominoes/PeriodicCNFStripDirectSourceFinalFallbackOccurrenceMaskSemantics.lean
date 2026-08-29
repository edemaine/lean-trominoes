/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskData
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDescriptorArityListSemantics

/-! # Semantics of fallback-family occurrence masks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

/-- A constant descriptor mask is just one constant entry per represented
literal occurrence. -/
theorem descriptorOccurrenceMask_eq_replicate
    (active : Bool)
    (descriptors : List
      PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    descriptorOccurrenceMask active descriptors =
      List.replicate
        ((descriptors.map retainedFinalCopiedDescriptorArity).sum)
        active := by
  unfold descriptorOccurrenceMask
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      simp only [List.flatMap_cons, descriptorOccurrenceMaskBlock,
        List.map_cons, List.sum_cons]
      rw [induction, ← List.replicate_add]

end LeanTrominoes.PeriodicCNFStripReduction

end
