/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ThirteenMarkerPairBlockData

/-! # Semantics of thirteen-marker pair-block expansion -/

namespace LeanTrominoes
namespace ThirteenMarkerPairBlocks

theorem scan_thirteen {Marker Output : Type}
    (pairs : Fin 13 → List Output) (marker : Marker) :
    FiniteStateTransducer.scan (transition pairs) 0
        (List.replicate 13 marker) =
      (0, block pairs) := by
  unfold transition block
  rfl

theorem scan_replicate_mul_thirteen {Marker Output : Type}
    (pairs : Fin 13 → List Output) (marker : Marker) (count : Nat) :
    FiniteStateTransducer.scan (transition pairs) 0
        (List.replicate (13 * count) marker) =
      (0, (List.replicate count (block pairs)).flatten) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [show 13 * (count + 1) = 13 + 13 * count by omega,
        List.replicate_add, FiniteStateTransducer.scan_append,
        scan_thirteen]
      dsimp only
      rw [induction]
      simp only [List.replicate_succ, List.flatten_cons]

theorem output_replicate_mul_thirteen {Marker Output : Type}
    (pairs : Fin 13 → List Output) (marker : Marker) (count : Nat) :
    output pairs (List.replicate (13 * count) marker) =
      (List.replicate count (block pairs)).flatten := by
  unfold output FiniteStateTransducer.output
  rw [scan_replicate_mul_thirteen]
  simp only [List.append_nil]

end ThirteenMarkerPairBlocks
end LeanTrominoes
