/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.ThirteenMarkerPairBlockSemantics

/-! # Polynomial-time thirteen-marker pair-block expansion -/

noncomputable section

namespace LeanTrominoes
namespace ThirteenMarkerPairBlocks

open Computability Turing

noncomputable def computableInPolyTime
    {Marker Output : Type} [Fintype Marker] [Fintype Output]
    [Inhabited Output] (pairs : Fin 13 → List Output) :
    TM2ComputableInPolyTime id id (output (Marker := Marker) pairs) :=
  FiniteStateTransducer.computableInPolyTime
    0 (transition pairs) (fun _ => [])

end ThirteenMarkerPairBlocks
end LeanTrominoes

end
