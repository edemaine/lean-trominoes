/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalDrawing

/-!
# Residue representatives at vertical drawing boundaries
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- Row `-1` projects to the final row of a positive predecessor-encoded
period. -/
theorem residue_neg_one_val_int (periodPred : Nat) :
    ((residue (-1) periodPred).val : Int) = periodPred := by
  rw [residue_val_int]
  let modulus : Int := periodPred + 1
  have modulusPositive : 0 < modulus := by
    simp [modulus]
  calc
    (-1 : Int) % modulus = (-1 + modulus) % modulus := by
      rw [Int.add_emod]
      simp
    _ = (periodPred : Int) % modulus := by
      congr 1
      simp [modulus]
    _ = periodPred :=
      Int.emod_eq_of_lt (by positivity) (by simp [modulus])

/-- One full positive predecessor-encoded period projects to row `0`. -/
theorem residue_period_val_int (periodPred : Nat) :
    ((residue (periodPred + 1 : Int) periodPred).val : Int) = 0 := by
  rw [residue_val_int]
  simp

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
