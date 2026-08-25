/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData

/-! # One-word semantics of guarded presence projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedPresenceFieldProjector

theorem scan_skipBits (activeValue : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan (transition activeValue) .skip
        (bits.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_semanticWord (activeValue : Bool)
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition activeValue) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField (value activeValue key)) := by
  cases key with
  | none =>
      cases activeValue <;> rfl
  | some key =>
      simp only [semanticWord, DelimitedBinaryWords.wordTokens,
        List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [scan_skipBits]
      cases activeValue <;> rfl

end GuardedPresenceFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
