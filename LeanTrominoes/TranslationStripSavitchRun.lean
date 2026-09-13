/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSavitchRun
import LeanTrominoes.TranslationStripSavitchLeaf

/-! # Orientation-restricted strip SavitchRun certificates

The input adapters and relation-independent bounds reuse the existing strip solver.
-/

namespace LeanTrominoes.TranslationStrip.Savitch
open PolyominoStripWindow PolyominoStripWindow.Savitch

open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def countdownBudget (bits suffixSpace : Nat) : Nat :=
  GenericSavitchReach.reachBudget (stateBudget bits suffixSpace)
    (baseCoefficient*(stateBudget bits suffixSpace+1)) (fuelBits bits)

theorem countdown_fits (cells : Bool → List Cell) (height bound bits first last : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits (Code.flatIterate (DivideEvalPartrec.stepCode baseCode))
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList (suffix cells height bound) 0 (2^bits)
        (divideEvalInitial bits first last))
      (GenericSavitchStep.flatProgramList (suffix cells height bound) 0 (2^bits)
        (((divideEvalStep (2^bits) (TranslationStrip.check cells height bound))^[divideEvalFuel (2^bits) bits])
          (divideEvalInitial bits first last)))
      (countdownBudget bits (encodedListSpace (suffix cells height bound))) := by
  apply GenericSavitchReach.iterate_fits (suffix cells height bound) baseCode (TranslationStrip.check cells height bound)
    (baseCost cells height bound) (base_fits cells height bound bounded) 0 (2^bits)
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
    (stateBudget bits (encodedListSpace (suffix cells height bound)))
    (baseCoefficient*(stateBudget bits (encodedListSpace (suffix cells height bound))+1)) (fuelBits bits)
    (fuel_length_le bits)
  · intro taken ht
    exact state_space_le _ _ bits first last taken hf hl
  · intro taken ht
    have h := state_space_le (suffix cells height bound) (TranslationStrip.check cells height bound) bits first last taken hf hl
    exact Nat.mul_le_mul_left baseCoefficient (Nat.add_le_add_right h 1)

end LeanTrominoes.TranslationStrip.Savitch
