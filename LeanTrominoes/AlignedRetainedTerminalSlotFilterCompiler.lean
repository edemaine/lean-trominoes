/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteRoleSlotUnaryDecoderCompiler
import LeanTrominoes.FiniteRoleSlotUnaryDecoderSemantics
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Filtering aligned retained-terminal slots -/

noncomputable section

namespace LeanTrominoes
namespace AlignedRetainedTerminalSlotFilter

open Computability Turing

abbrev Slot := FiniteRoleSlotUnaryDecoder.Slot
abbrev Pair := Bool × Slot

def maskBase (active : Bool) : Nat :=
  8 * (Fintype.equivFin Bool active).val

def maskBases (controls : List Bool) : List Nat :=
  controls.map maskBase

def slotValues (slots : List Slot) : List Nat :=
  slots.map Fin.val

def codes (controls : List Bool) (slots : List Slot) : List Nat :=
  AlignedUnaryListClosure.added
    (maskBases controls) (slotValues slots)

def retainPair (pair : Pair) : List Slot :=
  if pair.1 then [pair.2] else []

def retainedPairs (pairs : List Pair) : List Slot :=
  pairs.flatMap retainPair

/-- Declarative positional filter, truncated when either list ends. -/
def selected (controls : List Bool) (slots : List Slot) : List Slot :=
  retainedPairs (List.zip controls slots)

private theorem decoded_codes (controls : List Bool) (slots : List Slot) :
    FiniteRoleSlotUnaryDecoder.pairs (Role := Bool)
        (codes controls slots) =
      List.zip controls slots := by
  induction controls generalizing slots with
  | nil =>
      simp [codes, maskBases, slotValues,
        AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums,
        FiniteRoleSlotUnaryDecoder.pairs]
  | cons active controls induction =>
      cases slots with
      | nil =>
          simp [codes, maskBases, slotValues,
            AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums,
            FiniteRoleSlotUnaryDecoder.pairs]
      | cons slot slots =>
          simp only [codes, maskBases, slotValues, List.map_cons,
            AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums,
            FiniteRoleSlotUnaryDecoder.pairs, List.zip_cons_cons]
          rw [show maskBase active + slot.val =
              8 * (Fintype.equivFin Bool active).val + slot.val by
            rfl]
          rw [FiniteRoleSlotUnaryDecoder.decode_role_slot_index]
          exact congrArg (List.cons (active, slot)) (induction slots)

@[simp] theorem retainedPairs_decoded_codes
    (controls : List Bool) (slots : List Slot) :
    retainedPairs
        (FiniteRoleSlotUnaryDecoder.pairs (Role := Bool)
          (codes controls slots)) =
      selected controls slots := by
  rw [decoded_codes]
  rfl

private noncomputable def retainedPairsComputableInPolyTime :
    TM2ComputableInPolyTime id id retainedPairs :=
  FiniteBlockTransducer.computableInPolyTime retainPair

/-- Equal-length Boolean controls and retained-terminal slots produced from
one input can be filtered positionally in polynomial time. -/
noncomputable def selectedComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (controls : Input → List Bool)
    (slots : Input → List Slot)
    (lengthEq : ∀ input,
      (controls input).length = (slots input).length)
    (controlCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool
        encodeInput id controls)
    (slotCompiler :
      @TM2ComputableInPolyTime
        Input (List Slot) InputSymbol Slot
        encodeInput id slots) :
    @TM2ComputableInPolyTime
      Input (List Slot) InputSymbol Slot
      encodeInput id
      (fun input => selected (controls input) (slots input)) := by
  let maskBaseCompiler :=
    TM2CompositionMachine.computableInPolyTime controlCompiler
      (FiniteUnaryFieldMap.computableInPolyTime maskBase)
  let slotValueCompiler :=
    TM2CompositionMachine.computableInPolyTime slotCompiler
      (FiniteUnaryFieldMap.computableInPolyTime Fin.val)
  let codeCompiler :=
    AlignedUnaryListClosure.addedComputableInPolyTime
      encodeInput
      (fun input => maskBases (controls input))
      (fun input => slotValues (slots input))
      (fun input => by
        simpa [maskBases, slotValues] using lengthEq input)
      maskBaseCompiler slotValueCompiler
  let decoded := TM2CompositionMachine.computableInPolyTime codeCompiler
    (FiniteRoleSlotUnaryDecoder.computableInPolyTime (Role := Bool))
  let filtered := TM2CompositionMachine.computableInPolyTime decoded
    retainedPairsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    filtered (fun input =>
      retainedPairs_decoded_codes (controls input) (slots input))

end AlignedRetainedTerminalSlotFilter
end LeanTrominoes

end
