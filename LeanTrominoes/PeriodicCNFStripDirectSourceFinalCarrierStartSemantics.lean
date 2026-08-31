/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartEqualitySemantics

/-! # Structural semantics of the final carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierStartSemanticsBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

local instance directFinalCarrierStartSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The named direct-source start and the generic final-carrier index start
are propositionally equal without evaluating the crossover family. -/
theorem directSourceFinalCarrierStart_structural
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartStructural decider symbols := by
  constructor
  exact (directSourceFinalCarrierStart_unfolded decider symbols).eq.trans
    (directSourceFinalCarrierStart_equalityIndependent
      decider symbols).eq

end LeanTrominoes.PeriodicCNFStripReduction

end
