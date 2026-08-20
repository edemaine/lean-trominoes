/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachineTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler wrapper for sparse assignment records -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseAssignmentTokenCompiler

open Computability Turing

/-- Compose any canonical sparse-assignment record emitter with the verified
fixed record parser and transport its exact prepared-motif equation. -/
def computableInPolyTimeOfEmitter
    {Input InputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {assignments : Input → List (Cell × Gadget.OrthogonalCellType)}
    (tromino : Tromino)
    (emitter : TM2ComputableInPolyTime encodeInput id
      (fun input => GadgetSparseAssignmentTokens.assignmentsTokens
        (assignments input))) :
    TM2ComputableInPolyTime encodeInput id
      (fun input =>
        GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
          tromino (assignments input)) := by
  let expanded := TM2CompositionMachine.computableInPolyTime emitter
    (GadgetSparseAssignmentTokenMachine.computableInPolyTime tromino)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq expanded
    (fun input => GadgetSparseAssignmentTokens.expand_assignmentsTokens
      tromino (assignments input))

end GadgetSparseAssignmentTokenCompiler
end LeanTrominoes
