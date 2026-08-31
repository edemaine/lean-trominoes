/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralDirections
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralOccurrenceConstructor

/-! # Public directions of matched final retained-carrier occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The explicit input equalities stored by a matched occurrence transport
its indexed public-direction theorem without unfolding its constructor. -/
theorem FinalCarrierTaggedLiteralOccurrence.publicDirections
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Fin 2}
    (matched : FinalCarrierTaggedLiteralOccurrence source taggedLink
      clauseIndex literal literalIndex)
    (nextSlice : Bool) :
    FinalCarrierTaggedLiteralPublicDirections source taggedLink clauseIndex
      literal literalIndex nextSlice := by
  have directions :=
    matched.occurrence.taggedLiteralPublicDirections nextSlice
  simpa only [matched.source_eq, matched.taggedLink_eq,
    matched.clauseIndex_eq, matched.literal_eq,
    matched.literalIndex_eq] using directions

end PeriodicEightOccurrenceSplit
end LeanTrominoes

