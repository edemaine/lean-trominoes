/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinData

/-! # Streaming the first and last symbol of every delimited block -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetDelimitedBlockEndpoints

open Computability Turing FiniteAlphabetDelimitedBlockJoin

variable {Alphabet : Type}

abbrev State (Alphabet : Type) := Option (Alphabet × Alphabet)

/-- A block needs only its first and most recent symbol in finite control.
An empty block emits the supplied fallback at both endpoints. -/
def transition (fallback : Alphabet) (state : State Alphabet) :
    Token Alphabet → State Alphabet × List (Alphabet × Alphabet)
  | .value value =>
      (some ((state.map Prod.fst).getD value, value), [])
  | .blockEnd => (none, [state.getD (fallback, fallback)])

def finish (_ : State Alphabet) : List (Alphabet × Alphabet) := []

def output (fallback : Alphabet) (input : List (Token Alphabet)) :
    List (Alphabet × Alphabet) :=
  FiniteStateTransducer.output none (transition fallback) finish input

/-- Summarizing arbitrary-length blocks uses a fixed finite-state machine. -/
noncomputable def computableInPolyTime [Fintype Alphabet] (fallback : Alphabet) :
    TM2ComputableInPolyTime id id (output fallback) := by
  letI : Inhabited Alphabet := ⟨fallback⟩
  exact FiniteStateTransducer.computableInPolyTime none (transition fallback) finish

private theorem scan_tail (fallback first previous : Alphabet)
    (tail : List Alphabet) :
    FiniteStateTransducer.scan (transition fallback) (some (first, previous))
      (tail.map Token.value ++ [.blockEnd]) =
      (none, [(first, tail.getLastD previous)]) := by
  induction tail generalizing previous with
  | nil => simp [FiniteStateTransducer.scan, transition]
  | cons value tail induction =>
      simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan,
        transition, Option.map_some, Option.getD_some]
      rw [induction]
      simp only [List.getLastD_cons, List.nil_append]

private theorem scan_block (fallback : Alphabet) (body : List Alphabet) :
    FiniteStateTransducer.scan (transition fallback) none (block body) =
      (none, [(body.headD fallback, body.getLastD fallback)]) := by
  cases body with
  | nil => simp [block, FiniteStateTransducer.scan, transition]
  | cons first tail =>
      simp only [block, List.map_cons, List.cons_append, FiniteStateTransducer.scan,
        transition, Option.map_none, Option.getD_none]
      rw [scan_tail]
      simp only [List.getLastD_cons, List.headD_cons, List.nil_append]

theorem output_block_append (fallback : Alphabet) (body : List Alphabet)
    (remaining : List (Token Alphabet)) :
    output fallback (block body ++ remaining) =
      (body.headD fallback, body.getLastD fallback) :: output fallback remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_block]
  simp [finish]

/-- Each input delimiter contributes exactly one endpoint pair, including
empty blocks, and the original block order is preserved. -/
@[simp] theorem output_blocks (fallback : Alphabet) (bodies : List (List Alphabet)) :
    output fallback (blocks bodies) =
      bodies.map (fun body => (body.headD fallback, body.getLastD fallback)) := by
  induction bodies with
  | nil => rfl
  | cons body bodies induction =>
      change output fallback (block body ++ blocks bodies) = _
      rw [output_block_append, induction]
      rfl

end LeanTrominoes.FiniteAlphabetDelimitedBlockEndpoints

end
