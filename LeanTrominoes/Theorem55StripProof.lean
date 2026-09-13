/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripMembership
import LeanTrominoes.Theorem55StripUnaryCorrect
import LeanTrominoes.Theorem55StripHardSourceCompiler

/-! # PSPACE-completeness of two-polyomino strip tiling -/

namespace LeanTrominoes.Theorem55
open Turing PeriodicCNFStripReduction

/-- Every finite-encoding PSPACE language reduces to the exact unary P/Q strip problem. -/
theorem strip_PSPACEHard : Complexity.PSPACEHard Theorem55StripEncoding.finEncoding stripProblem := by
  intro Input encoding language membership
  obtain ⟨decider⟩ := membership
  let reduce := fun input => Theorem55StripUnary.compiledInput
    (directSparseCompiledTrominoStrip decider .I input)
  let compiler := TM2CompositionMachine.computableInPolyTime
    (Theorem55StripHardSource.compiler decider) Theorem55StripUnary.compiler
  apply Complexity.PolyTimeManyOneReducible.of_computableInPolyTime reduce ⟨compiler⟩
  intro input
  exact (directSparseCompiledTrominoStrip_correct decider .I Gadget.iOrientationBehaviorCorrect input).trans
    (Theorem55StripUnary.compiledInput_correct _ (Theorem55StripHardSource.wellFormed decider input)).symm

/-- The fixed connected 15-omino P and an input disconnected Q yield PSPACE-complete
strip tiling, with arbitrary rotations and reflections and the original unary encoding. -/
theorem stripProved : stripStatement := ⟨strip_inPSPACE,strip_PSPACEHard⟩

end LeanTrominoes.Theorem55
