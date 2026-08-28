/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupMachine

/-! # Unary lookup through fixed-field expanded Boolean rows -/

namespace LeanTrominoes
namespace DelimitedBinaryWordFixedFieldRowExpansion

open LastTrueUnaryValueLookupMachine

private theorem lookupAux_falsePrefix
    (candidate : Nat) (count : Nat) (headValues : List Nat)
    (bits : List Bool) (values : List Nat)
    (headLength : headValues.length = count) :
    lookupAux candidate
        (List.replicate count false ++ bits) (headValues ++ values) =
      lookupAux candidate bits values := by
  induction count generalizing headValues candidate with
  | zero =>
      cases headValues with
      | nil => rfl
      | cons _ _ => simp at headLength
  | succ count induction =>
      cases headValues with
      | nil => simp at headLength
      | cons value headValues =>
          have tailLength : headValues.length = count :=
            Nat.succ.inj headLength
          rw [List.replicate_succ, List.cons_append]
          exact induction (headValues := headValues)
            (candidate := candidate) tailLength

private theorem lookupAux_expandedBit
    (candidate : Nat) (width index : Nat) (bit : Bool)
    (block : List Nat) (bits : List Bool) (values : List Nat)
    (indexLt : index < width) (blockLength : block.length = width) :
    lookupAux candidate
        (expandedBit width index bit ++ bits) (block ++ values) =
      lookupAux (if bit then block.getD index 0 else candidate)
        bits values := by
  induction width generalizing index block candidate with
  | zero => omega
  | succ width induction =>
      cases block with
      | nil => simp at blockLength
      | cons value block =>
          have tailLength : block.length = width := by
            simpa using blockLength
          cases index with
          | zero =>
              cases bit <;>
                simp only [expandedBit, List.cons_append, lookupAux,
                  List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte]
              · exact lookupAux_falsePrefix candidate width block bits values
                  tailLength
              · exact lookupAux_falsePrefix value width block bits values
                  tailLength
          | succ index =>
              have tailLt : index < width := by omega
              simp only [expandedBit, List.cons_append, lookupAux,
                List.getD_cons_succ]
              exact induction (index := index) (block := block)
                (candidate := candidate) tailLt tailLength

private theorem lookupAux_row_flatten
    (candidate width index : Nat) (bits : List Bool)
    (blocks : List (List Nat)) (indexLt : index < width)
    (aligned : List.Forall₂
      (fun _ block => block.length = width) bits blocks) :
    lookupAux candidate (row width index bits) blocks.flatten =
      lookupAux candidate bits
        (blocks.map fun block => block.getD index 0) := by
  induction aligned generalizing candidate with
  | nil => rfl
  | @cons bit block bits blocks blockLength aligned induction =>
      unfold row
      rw [List.flatMap_cons, List.flatten_cons]
      rw [lookupAux_expandedBit candidate width index bit block
        (bits.flatMap (expandedBit width index)) blocks.flatten
        indexLt blockLength]
      change lookupAux (if bit then block.getD index 0 else candidate)
        (row width index bits) blocks.flatten = _
      rw [induction]
      cases bit <;> rfl

/-- Looking up one expanded field row against fixed-width value blocks is
the same as looking up the corresponding field in the unexpanded row. -/
theorem lookup_row_flatten
    (width index : Nat) (bits : List Bool) (blocks : List (List Nat))
    (indexLt : index < width)
    (aligned : List.Forall₂
      (fun _ block => block.length = width) bits blocks) :
    lookup (row width index bits) blocks.flatten =
      lookup bits (blocks.map fun block => block.getD index 0) := by
  unfold lookup
  exact lookupAux_row_flatten 0 width index bits blocks indexLt aligned

end DelimitedBinaryWordFixedFieldRowExpansion
end LeanTrominoes
