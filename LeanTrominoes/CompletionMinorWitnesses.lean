/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionMinorData
import LeanTrominoes.FiniteTrominoCompletion

/-! # The paper's equal/not completion witnesses

These certificates establish existence for the two intended states of each
gadget. Exclusion of unintended states and composition are separate obligations.
Coordinates follow the ASCII figures, with y increasing downward.
-/

namespace LeanTrominoes.CompletionMinor

def leftPort : Tromino → Int | .I => 5 | .L => 2

def rightPort : Tromino → Int | .I => 14 | .L => 8

def bottom : Tromino → Int | .I => 9 | .L => 6

def output (gate : Gate) (value : Bool) : Bool :=
  match gate with | .equal => value | .negate => !value

/-- At the top, true leaves the right port for the neighboring brick.
At the bottom, true leaves the left port for the neighboring brick. -/
def externalPorts (t : Tromino) (topValue bottomValue : Bool) : Finset Cell :=
  {(if topValue then rightPort t else leftPort t,0),
   (if bottomValue then leftPort t else rightPort t,bottom t)}

def target (t : Tromino) (gate : Gate) (topValue bottomValue : Bool) : Finset Cell :=
  region t gate \ externalPorts t topValue bottomValue

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem solution_tiles (t : Tromino) (gate : Gate) (value : Bool) :
    IsFiniteTiling (fun _ => t.cells) (target t gate value (output gate value))
      (solution t gate value) := by
  cases t <;> cases gate <;> cases value <;> decide +kernel

set_option maxRecDepth 8192 in
theorem solution_retains (t : Tromino) (gate : Gate) (value : Bool) :
    prefill t gate ⊆ solution t gate value := by
  cases t <;> cases gate <;> cases value <;> decide +kernel

/-- Every intended equal/not state extends the actual preplaced trominoes. -/
theorem intended_state_completable (t : Tromino) (gate : Gate) (value : Bool) :
    t.Completable (target t gate value (output gate value) : Set Cell)
      (t.finiteFootprints (prefill t gate) : Set (Finset Cell)) :=
  t.completable_of_finiteTiling _ _ _ (solution_tiles t gate value) (solution_retains t gate value)

end LeanTrominoes.CompletionMinor
