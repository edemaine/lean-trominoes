/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence

/-! # Matched occurrences of tagged final retained-bend literals -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- An indexed occurrence together with explicit equalities to the tagged
bend literal from which it was constructed. -/
structure FinalBendTaggedLiteralOccurrence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2) where
  occurrence : FinalBendIndexedOccurrence Variable
  source_eq : occurrence.source = source
  taggedBend_eq : occurrence.taggedBend = taggedBend
  clauseIndex_eq : occurrence.clauseIndex = clauseIndex
  literal_eq : occurrence.literal = literal
  literalIndex_eq : occurrence.literalIndex = literalIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
