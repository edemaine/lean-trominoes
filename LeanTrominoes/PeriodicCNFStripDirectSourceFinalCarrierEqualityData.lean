/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts

/-! # Shared structural equality for direct final-carrier data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Equality synthesized at the original direct tagged-link definition. -/
noncomputable def directSourceFinalOriginalBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  inferInstance

/-- Corresponding equality on retained direct-source variables. -/
noncomputable def directSourceFinalOriginalVariableDecidableEq :
    DecidableEq Variable :=
  @PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
    (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq

/-- Shared structural equality for direct three-CNF variables. -/
noncomputable def directSourceFinalStructuralBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

/-- Shared structural equality for direct final variables. -/
noncomputable def directSourceFinalStructuralVariableDecidableEq :
    DecidableEq Variable :=
  @PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
    (ThreeCNFVariable Nat) directSourceFinalStructuralBaseDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
