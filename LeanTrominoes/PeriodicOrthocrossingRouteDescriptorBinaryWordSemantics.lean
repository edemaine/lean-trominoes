/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData

/-! # Exact semantics of binary route-descriptor words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWords

open RouteDescriptorScanTokens

theorem scan_units (control : Control) (number : Nat) :
    FiniteStateTransducer.scan transition control
        (List.replicate number .unit) =
      (control,
        List.replicate number (.bit false : DelimitedBinaryWords.Token)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

theorem scan_field (control : Control) (number : Nat) :
    FiniteStateTransducer.scan transition control (field number) =
      (nextControl control,
        List.replicate number
            (.bit false : DelimitedBinaryWords.Token) ++
          if control.val = 10 then [.bit true, .wordEnd]
          else [.bit true]) := by
  rw [show field number =
      List.replicate number .unit ++ [.fieldEnd] by rfl]
  rw [FiniteStateTransducer.scan_append, scan_units]
  simp only [FiniteStateTransducer.scan, transition, List.append_nil]

theorem scan_eleven_fields
    (a b c d e f g h i j k : Nat) :
    FiniteStateTransducer.scan transition 0
        (fields [a, b, c, d, e, f, g, h, i, j, k]) =
      (0,
        ([a, b, c, d, e, f, g, h, i, j, k].flatMap fun number =>
            List.replicate number
                (.bit false : DelimitedBinaryWords.Token) ++ [.bit true]) ++
          [.wordEnd]) := by
  simp only [fields, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [FiniteStateTransducer.scan_append, scan_field]
  dsimp [nextControl]
  rw [scan_field]
  dsimp [nextControl]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem scan_record (descriptor : RouteDescriptor) :
    FiniteStateTransducer.scan transition 0 (record descriptor) =
      (0, DelimitedBinaryWords.wordTokens (descriptorWord descriptor)) := by
  rcases descriptor with ⟨vertexCount, edgeCount, edgeIndex,
    sourceVertexIndex, targetVertexIndex, sourcePortRank, targetPortRank,
    ⟨horizontal, vertical⟩⟩
  change FiniteStateTransducer.scan transition 0
      (.recordStart :: fields
        [vertexCount, edgeCount, edgeIndex, sourceVertexIndex,
          targetVertexIndex, sourcePortRank, targetPortRank,
          horizontal.toNat, (-horizontal).toNat,
          vertical.toNat, (-vertical).toNat]) = _
  simp only [FiniteStateTransducer.scan, transition]
  rw [scan_eleven_fields]
  simp only [descriptorWord, RouteDescriptor.unaryFields, signedUnaryFields,
    fieldWord, DelimitedBinaryWords.wordTokens, List.map_flatMap,
    List.map_append, List.map_replicate, List.map_singleton,
    List.append_assoc]
  rfl

theorem scan_encode (descriptors : List RouteDescriptor) :
    FiniteStateTransducer.scan transition 0
        (RouteDescriptorScanTokens.encode descriptors) =
      (0, DelimitedBinaryWords.encode (words descriptors)) := by
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      rw [show RouteDescriptorScanTokens.encode
            (descriptor :: descriptors) =
          record descriptor ++ RouteDescriptorScanTokens.encode descriptors
        by rfl]
      rw [FiniteStateTransducer.scan_append, scan_record]
      dsimp
      rw [induction]
      rfl

/-- Canonical normalized records become exactly the canonical encoded list
of descriptor words. -/
theorem tokens_encode (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorScanTokens.encode descriptors) =
      DelimitedBinaryWords.encode (words descriptors) := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_encode]
  simp only [finish, List.append_nil]

end RouteDescriptorBinaryWords
end PeriodicOrthocrossing
end LeanTrominoes
