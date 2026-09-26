/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSerialization
import LeanTrominoes.FiniteUnaryFieldMapCompiler

/-! # Optional unary payloads retaining one delimiter per row -/
noncomputable section
namespace LeanTrominoes.UnaryOptionalBlocks
open Computability Turing FiniteStateTransducer
open UnaryFieldEncoderMachine (unaryField)
open FiniteAlphabetDelimitedBlockJoin (block blocks)
abbrev Token := FiniteAlphabetDelimitedBlockJoin.Token UnaryFieldEncoderMachine.Symbol

inductive State
  | read (nonzero : Bool)
  | emit (keep : Bool)
  deriving Fintype

def transition : State → Token → State × List Token
  | _, .blockEnd => (.read false, [.blockEnd])
  | .read _, .value .unit => (.read true, [])
  | .read keep, .value .delimiter => (.emit keep, [])
  | .emit keep, .value value => (.emit keep, if keep then [.value value] else [])

private theorem scan_payload (keep : Bool) (payload : List UnaryFieldEncoderMachine.Symbol) :
    scan transition (.emit keep) (payload.map .value ++ [.blockEnd]) =
      (.read false, block (if keep then payload else [])) := by
  induction payload with
  | nil => cases keep <;> rfl
  | cons value payload ih =>
      cases keep <;> simp [scan, transition, ih, block]

private theorem scan_block (keep : Bool) (payload : List UnaryFieldEncoderMachine.Symbol) :
    scan transition (.read false) (block (unaryField keep.toNat ++ payload)) =
      (.read false, block (if keep then payload else [])) := by
  cases keep with
  | false => simpa [block, unaryField, scan, transition] using scan_payload false payload
  | true => simpa [block, unaryField, scan, transition] using scan_payload true payload

private theorem scan_blocks (items : List (Bool × List UnaryFieldEncoderMachine.Symbol)) :
    scan transition (.read false) (blocks (items.map (fun item => unaryField item.1.toNat ++ item.2))) =
      (.read false, blocks (items.map (fun item => if item.1 then item.2 else []))) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.map_cons, blocks, List.flatMap_cons] at ih ⊢
      simp only [scan_append, scan_block]
      rw [ih]

/-- Discarding a payload leaves its row boundary in place for later joins. -/
def compiler {Source Index : Type} [Fintype Source] [Inhabited Source]
    {rows : List Source → List Index}
    {keep : List Source → Index → Bool} {body : List Source → Index → List UnaryFieldEncoderMachine.Symbol}
    (control : TM2ComputableInPolyTime id id (fun s => (rows s).map (keep s)))
    (payload : UnaryColumn.BlocksCompiler rows body) :
    UnaryColumn.BlocksCompiler rows (fun s row => if keep s row then body s row else []) := by
  let flags : UnaryColumn.Compiler rows (fun s row => (keep s row).toNat) :=
    TM2ComputableInPolyTime.of_eq
      (TM2CompositionMachine.computableInPolyTime control (FiniteUnaryFieldMap.computableInPolyTime Bool.toNat))
      (fun s => by simp [FiniteUnaryFieldMap.values, List.map_map])
  let joined := UnaryColumn.appendBlocks (UnaryColumn.blocks flags) payload
  let physical := TM2CompositionMachine.computableInPolyTime joined
    (FiniteStateTransducer.computableInPolyTime (.read false) transition (fun _ => []))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have scanned := scan_blocks ((rows s).map (fun row => (keep s row, body s row)))
  simpa only [output, List.map_map, Function.comp_def, scanned, List.append_nil] using
    congrArg Prod.snd scanned

end LeanTrominoes.UnaryOptionalBlocks
end
