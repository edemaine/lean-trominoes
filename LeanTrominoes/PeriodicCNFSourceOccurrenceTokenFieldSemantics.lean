/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenData

/-! # Exact flat-field parsing for occurrence tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Turing

@[simp] theorem nativeBit_partrecBit (bit : Bool) :
    nativeBit (Complexity.partrecBit bit) = bit := by
  cases bit <;> rfl

theorem scan_atom_bits (remaining index : Fin 3) (bits : List Bool) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .atom)
        (bits.map Complexity.partrecBit) =
      (.literal remaining index .atom,
        bits.map Token.atomBit) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [FiniteStateTransducer.scan, transition,
          Complexity.partrecBit, induction]

theorem scan_offset_bits (remaining index : Fin 3) (bits : List Bool) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .horizontalOffset)
        (bits.map Complexity.partrecBit) =
      (.literal remaining index .horizontalOffset,
        bits.map Token.offsetBit) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [FiniteStateTransducer.scan, transition,
          Complexity.partrecBit, induction]

theorem scan_vertical_bits (remaining index : Fin 3) (bits : List Bool) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .verticalOffset)
        (bits.map Complexity.partrecBit) =
      (.literal remaining index .verticalOffset, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [FiniteStateTransducer.scan, transition,
          Complexity.partrecBit, induction]

theorem scan_polarity_bits (remaining index : Fin 3) (bits : List Bool) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .polarity)
        (bits.map Complexity.partrecBit) =
      (.literal remaining index .polarity, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [FiniteStateTransducer.scan, transition,
          Complexity.partrecBit, induction]

theorem scan_clauseCount_bits (bits : List Bool) :
    FiniteStateTransducer.scan transition .clauseCount
        (bits.map Complexity.partrecBit) =
      (.clauseCount, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [FiniteStateTransducer.scan, transition,
          Complexity.partrecBit, induction]

theorem scan_atom_field (remaining index : Fin 3) (atom : Nat) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .atom)
        (PartrecToTM2.trNat atom ++ [.cons]) =
      (.literal remaining index .horizontalOffset,
        atomTokens atom ++ [.atomEnd]) := by
  rw [Complexity.partrec_trNat_eq_map_encodeNat,
    FiniteStateTransducer.scan_append,
    scan_atom_bits]
  simp [FiniteStateTransducer.scan, transition, atomTokens,
    Complexity.partrec_trNat_eq_map_encodeNat, List.map_map]

theorem scan_offset_field (remaining index : Fin 3) (offset : Int) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .horizontalOffset)
        (PartrecToTM2.trNat (Encodable.encode offset) ++ [.cons]) =
      (.literal remaining index .verticalOffset,
        offsetTokens offset ++ [.offsetEnd]) := by
  rw [Complexity.partrec_trNat_eq_map_encodeNat,
    FiniteStateTransducer.scan_append,
    scan_offset_bits]
  simp [FiniteStateTransducer.scan, transition, offsetTokens,
    Complexity.partrec_trNat_eq_map_encodeNat, List.map_map]

theorem scan_vertical_field (remaining index : Fin 3) (offset : Int) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .verticalOffset)
        (PartrecToTM2.trNat (Encodable.encode offset) ++ [.cons]) =
      (.literal remaining index .polarity, []) := by
  rw [Complexity.partrec_trNat_eq_map_encodeNat,
    FiniteStateTransducer.scan_append,
    scan_vertical_bits]
  simp [FiniteStateTransducer.scan, transition]

theorem scan_polarity_field (remaining index : Fin 3) (value : Bool) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .polarity)
        (PartrecToTM2.trNat
          (PeriodicCNFFlatEncoding.encodeBoolField value) ++ [.cons]) =
      nextLiteral remaining index := by
  rw [Complexity.partrec_trNat_eq_map_encodeNat,
    FiniteStateTransducer.scan_append,
    scan_polarity_bits]
  simp [FiniteStateTransducer.scan, transition]

/-- Parsing the four fields of one literal retains only its atom and
horizontal offset, then emits the correct literal terminator/next marker. -/
theorem scan_literalFields (remaining index : Fin 3)
    (literal : PeriodicLiteral Nat) :
    FiniteStateTransducer.scan transition
        (.literal remaining index .atom)
        (PartrecToTM2.trList
          (PeriodicCNFFlatEncoding.literalFields literal)) =
      let next := nextLiteral remaining index
      (next.1,
        atomTokens literal.atom ++ [.atomEnd] ++
          offsetTokens literal.offset.1 ++ [.offsetEnd] ++ next.2) := by
  rcases literal with ⟨atom, ⟨horizontal, vertical⟩, value⟩
  simp only [PeriodicCNFFlatEncoding.literalFields, PartrecToTM2.trList]
  rw [show
    PartrecToTM2.trNat atom ++ .cons ::
        (PartrecToTM2.trNat (Encodable.encode horizontal) ++ .cons ::
          (PartrecToTM2.trNat (Encodable.encode vertical) ++ .cons ::
            (PartrecToTM2.trNat
              (PeriodicCNFFlatEncoding.encodeBoolField value) ++ [.cons]))) =
      (PartrecToTM2.trNat atom ++ [.cons]) ++
        ((PartrecToTM2.trNat (Encodable.encode horizontal) ++ [.cons]) ++
          ((PartrecToTM2.trNat (Encodable.encode vertical) ++ [.cons]) ++
            (PartrecToTM2.trNat
              (PeriodicCNFFlatEncoding.encodeBoolField value) ++ [.cons]))) by
    simp [List.append_assoc]]
  rw [FiniteStateTransducer.scan_append, scan_atom_field]
  simp only
  rw [FiniteStateTransducer.scan_append, scan_offset_field]
  simp only
  rw [FiniteStateTransducer.scan_append, scan_vertical_field]
  simp only
  rw [scan_polarity_field]
  simp [List.append_assoc]

/-- Canonical arity fields zero through three select the exact bounded
clause/literal-start tokens. -/
theorem scan_arityField (arity : Nat) (width : arity ≤ 3) :
    FiniteStateTransducer.scan transition (.arity .start)
        (PartrecToTM2.trNat arity ++ [.cons]) =
      beginClause (clauseArity arity) := by
  have cases : arity = 0 ∨ arity = 1 ∨ arity = 2 ∨ arity = 3 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

/-- The leading clause-count field is discarded exactly. -/
theorem scan_clauseCountField (count : Nat) :
    FiniteStateTransducer.scan transition .clauseCount
        (PartrecToTM2.trNat count ++ [.cons]) =
      (.arity .start, []) := by
  rw [Complexity.partrec_trNat_eq_map_encodeNat,
    FiniteStateTransducer.scan_append,
    scan_clauseCount_bits]
  rfl

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes
