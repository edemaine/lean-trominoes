/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import Mathlib.Data.List.FinRange

/-! # Expanding thirteen-marker groups into fixed pair blocks -/

namespace LeanTrominoes
namespace ThirteenMarkerPairBlocks

/-- Advance modulo thirteen and emit the pair assigned to the current marker
position. -/
def transition {Marker Output : Type}
    (pairs : Fin 13 → List Output) :
    Fin 13 → Marker → Fin 13 × List Output :=
  fun index _marker => (index + 1, pairs index)

/-- One complete thirteen-position output block. -/
def block {Output : Type} (pairs : Fin 13 → List Output) : List Output :=
  (List.finRange 13).flatMap pairs

/-- Finite-state expansion of a marker stream into successive pair fields. -/
def output {Marker Output : Type} (pairs : Fin 13 → List Output)
    (markers : List Marker) : List Output :=
  FiniteStateTransducer.output 0 (transition pairs) (fun _ => []) markers

end ThirteenMarkerPairBlocks
end LeanTrominoes
