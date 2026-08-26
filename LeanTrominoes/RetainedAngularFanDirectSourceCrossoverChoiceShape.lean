/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-! # Shape of successful raw crossover choices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Inverting a successful raw crossover lookup exposes its bounded local
clause and literal indices and the exact choice record. -/
theorem retainedDirectSourceRouteChoice?_crossover_eq_some_iff_shape
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (localClauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice?
          formula (.crossover crossing localClauseIndex) literalIndex =
        some choice) :
    ∃ (localClauseIndexLt : localClauseIndex < 26)
        (literalIndexLt :
          literalIndex <
            (retainedDirectSourcePrefixChoices
              (.crossover ⟨localClauseIndex, localClauseIndexLt⟩)).length),
      choice = {
        origin := crossingMacroOrigin crossing
        kind := .crossover ⟨localClauseIndex, localClauseIndexLt⟩
        index := ⟨literalIndex, literalIndexLt⟩
      } := by
  simp only [retainedDirectSourceRouteChoice?] at lookup
  split at lookup
  next localClauseIndexLt =>
    split at lookup
    next literalIndexLt =>
      simp only [Option.some.injEq] at lookup
      exact ⟨localClauseIndexLt, literalIndexLt, lookup.symm⟩
    next => contradiction
  next => contradiction

end PeriodicEightOccurrenceSplit
end LeanTrominoes
