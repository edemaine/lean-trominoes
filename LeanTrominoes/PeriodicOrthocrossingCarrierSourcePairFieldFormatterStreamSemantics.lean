/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterWordSemantics

/-! # Stream semantics of the source-pair field formatter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

theorem scan_sourcePairs
    (sourcePairs : List CarrierNodeSourceKeys.SourceKeyPair) :
    FiniteStateTransducer.scan transition .begin
        (UnaryFieldEncoderMachine.unaryFields
          (sourcePairs.flatMap fun sourcePair =>
            CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.sourcePairFields
              (some sourcePair))) =
      (.begin, DelimitedBinaryWords.encode (words sourcePairs)) := by
  induction sourcePairs with
  | nil => rfl
  | cons sourcePair sourcePairs induction =>
      rw [List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append,
        FiniteStateTransducer.scan_append, scan_sourcePair]
      dsimp
      rw [induction]
      rfl

/-- Formatting a list of twelve-field representatives reconstructs exactly
the corresponding guarded source-pair word stream. -/
@[simp] theorem output_sourcePairs
    (sourcePairs : List CarrierNodeSourceKeys.SourceKeyPair) :
    output
        (UnaryFieldEncoderMachine.unaryFields
          (sourcePairs.flatMap fun sourcePair =>
            CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.sourcePairFields
              (some sourcePair))) =
      DelimitedBinaryWords.encode (words sourcePairs) := by
  unfold output FiniteStateTransducer.output
  rw [scan_sourcePairs]
  simp [finish]

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing
