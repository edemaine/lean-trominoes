/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordData

/-! # Semantics of route-descriptor target atom words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorTargetAtomWords

open RouteDescriptorScanTokens

theorem scan_units (control : Control) (number : Nat) :
    FiniteStateTransducer.scan transition control
        (List.replicate number .unit) =
      (control,
        if control.val = 4 then
          List.replicate number
            (.bit false : DelimitedBinaryWords.Token)
        else []) := by
  induction number with
  | zero =>
      by_cases selected : control.val = 4 <;>
        simp [selected, FiniteStateTransducer.scan]
  | succ number induction =>
      rw [List.replicate_succ, FiniteStateTransducer.scan]
      simp only [transition]
      rw [induction]
      by_cases selected : control.val = 4 <;>
        simp [selected, List.replicate_succ]

theorem scan_field (control : Control) (number : Nat) :
    FiniteStateTransducer.scan transition control (field number) =
      (nextControl control,
        if control.val = 4 then
          List.replicate number
              (.bit false : DelimitedBinaryWords.Token) ++
            [.bit true, .wordEnd]
        else []) := by
  rw [show field number =
      List.replicate number .unit ++ [.fieldEnd] by rfl]
  rw [FiniteStateTransducer.scan_append, scan_units]
  simp only [FiniteStateTransducer.scan, transition, List.append_nil]
  by_cases selected : control.val = 4 <;> simp [selected]

theorem scan_eleven_fields
    (a b c d e f g h i j k : Nat) :
    FiniteStateTransducer.scan transition 0
        (fields [a, b, c, d, e, f, g, h, i, j, k]) =
      (0,
        List.replicate e
            (.bit false : DelimitedBinaryWords.Token) ++
          [.bit true, .wordEnd]) := by
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
  simp

theorem scan_record (descriptor : RouteDescriptor) :
    FiniteStateTransducer.scan transition 0 (record descriptor) =
      (0, DelimitedBinaryWords.wordTokens (word descriptor)) := by
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
  simp [word, CarrierKeyWords.natField,
    DelimitedBinaryWords.wordTokens, List.append_assoc]

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

/-- Physical projection is exactly the encoded semantic target-word list. -/
theorem tokens_encode (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorScanTokens.encode descriptors) =
      DelimitedBinaryWords.encode (words descriptors) := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_encode]
  simp [finish]

end RouteDescriptorTargetAtomWords
end PeriodicOrthocrossing
end LeanTrominoes
