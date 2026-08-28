/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordCleanupCompiler

/-! # Semantics of routed-variable compact atom-word cleanup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordCleanup

private theorem scan_terminalBody (bits : List Bool) :
    FiniteStateTransducer.scan transition .terminalBody
        (bits.map .bit ++ [.wordEnd]) =
      (.between .sourceAtom, bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

private theorem scan_sourceAtomSkip (bits : List Bool) :
    FiniteStateTransducer.scan transition .sourceAtomSkip
        (bits.map .bit ++ [.wordEnd]) =
      (.between .terminal, [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

private theorem scan_sourceAtomRoute (bits : List Bool) :
    FiniteStateTransducer.scan transition .sourceAtomRoute
        (bits.map .bit ++ [.wordEnd]) =
      (.between .terminal,
        (firstNatField bits).map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, transition, firstNatField]
        rw [induction]
        rfl
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, transition, firstNatField,
          List.map_singleton]
        rw [scan_sourceAtomSkip]
        rfl

private theorem scan_discard (kind : Kind) (bits : List Bool) :
    FiniteStateTransducer.scan transition (.discard kind)
        (bits.map .bit ++ [.wordEnd]) =
      (.between kind.next, []) := by
  induction bits with
  | nil => cases kind <;> rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_wordTokens (kind : Kind) (guarded : List Bool) :
    FiniteStateTransducer.scan transition (.between kind)
        (DelimitedBinaryWords.wordTokens guarded) =
      (.between kind.next,
        DelimitedBinaryWords.encode ⟨word kind guarded⟩) := by
  cases guarded with
  | nil => cases kind <;> rfl
  | cons active bits =>
      cases active
      · cases kind <;>
          simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
            List.cons_append, FiniteStateTransducer.scan, transition,
            word, DelimitedBinaryWords.encode]
        all_goals rw [scan_discard]
        all_goals simp [Kind.next]
      · cases kind with
        | terminal =>
            simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
              List.cons_append, FiniteStateTransducer.scan, transition,
              word, DelimitedBinaryWords.encode, List.flatMap_cons,
              List.flatMap_nil, List.append_nil]
            rw [scan_terminalBody]
            simp [DelimitedBinaryWords.wordTokens, Kind.next]
        | sourceAtom =>
            simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
              List.cons_append, FiniteStateTransducer.scan, transition,
              word, DelimitedBinaryWords.encode, List.flatMap_cons,
              List.flatMap_nil, List.append_nil]
            rw [scan_sourceAtomRoute]
            simp [DelimitedBinaryWords.wordTokens, Kind.next]

theorem scan_encodeFrom (kind : Kind) (guarded : List (List Bool)) :
    FiniteStateTransducer.scan transition (.between kind)
        (DelimitedBinaryWords.encode ⟨guarded⟩) =
      (.between (guarded.foldl (fun kind _ => kind.next) kind),
        DelimitedBinaryWords.encode ⟨wordsFrom kind guarded⟩) := by
  induction guarded generalizing kind with
  | nil => rfl
  | cons guarded rest induction =>
      rw [show DelimitedBinaryWords.encode ⟨guarded :: rest⟩ =
          DelimitedBinaryWords.wordTokens guarded ++
            DelimitedBinaryWords.encode ⟨rest⟩ by rfl,
        FiniteStateTransducer.scan_append,
        scan_wordTokens]
      dsimp
      rw [induction kind.next]
      simp only [wordsFrom, List.foldl_cons]
      congr 1
      change
        DelimitedBinaryWords.encode ⟨word kind guarded⟩ ++
            DelimitedBinaryWords.encode ⟨wordsFrom kind.next rest⟩ =
          DelimitedBinaryWords.encode
            ⟨word kind guarded ++ wordsFrom kind.next rest⟩
      unfold DelimitedBinaryWords.encode
      rw [List.flatMap_append]

/-- Physical cleanup is exactly the delimiter encoding of alternating
sentinel removal and compact terminal/source-atom retagging. -/
@[simp] theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (compact input) := by
  rcases input with ⟨guarded⟩
  unfold tokens FiniteStateTransducer.output compact words
  rw [scan_encodeFrom]
  simp [finish]

end RoutedVariableCompactAtomWordCleanup
end LeanTrominoes.PeriodicOrthocrossing
