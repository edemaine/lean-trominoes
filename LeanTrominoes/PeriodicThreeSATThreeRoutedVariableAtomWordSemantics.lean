/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityNormalizedClauseAtomWordSemantics
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedClauses

/-! # Atom-word column of canonical routed-variable clauses -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Canonical routed-variable clauses flatten to the repeated endpoint-word
block of each final-site normalized equality link. -/
theorem canonicalWrappedNormalizedRoutedVariableClauses_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (word : WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable) → List Bool) :
    (canonicalWrappedNormalizedRoutedVariableClauses source).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      (canonicalWrappedNormalizedRoutedVariableLinks source).flatMap
        fun link => [word link.first, word link.second,
          word link.first, word link.second] := by
  unfold canonicalWrappedNormalizedRoutedVariableClauses
  exact PeriodicEquality.normalizedClauses_atomWords _ _

end PeriodicThreeSATThree
end LeanTrominoes
