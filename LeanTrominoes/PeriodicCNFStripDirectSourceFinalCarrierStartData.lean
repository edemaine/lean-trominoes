/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartFamilyData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierEqualityData

/-! # Structural final-carrier start certificates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierStartDataBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

/-- Generic crossover-prefix length under structural final-variable equality. -/
def directSourceFinalCarrierStructuralStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalCarrierStartFamily decider symbols
    directSourceFinalStructuralVariableDecidableEq

/-- Opaque certificate that the public carrier start uses the structural
equality implementation of the generic crossover prefix. -/
structure DirectSourceFinalCarrierStartStructural
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStart decider symbols =
    directSourceFinalCarrierStructuralStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
