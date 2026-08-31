/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence

/-! # Matched occurrences of tagged final retained-carrier literals -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- An indexed occurrence together with explicit equalities to the tagged
carrier literal from which it was constructed. -/
structure FinalCarrierTaggedLiteralOccurrence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2) where
  occurrence : FinalCarrierIndexedOccurrence Variable
  source_eq : occurrence.source = source
  taggedLink_eq : occurrence.taggedLink = taggedLink
  clauseIndex_eq : occurrence.clauseIndex = clauseIndex
  literal_eq : occurrence.literal = literal
  literalIndex_eq : occurrence.literalIndex = literalIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes

