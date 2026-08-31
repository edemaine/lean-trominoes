/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputOccurrence
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralOccurrenceDirections

/-! # Literal directions from packaged final retained-carrier link input -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Add one selected literal to packaged tagged-link evidence and recover its
exact public normalized route directions. -/
theorem FinalCarrierTaggedLinkInput.literalPublicDirections
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput
      source taggedLink clauseIndex)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈
        (normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula source) taggedLink).zipIdx)
    (nextSlice : Bool) :
    FinalCarrierTaggedLiteralPublicDirections
      source taggedLink clauseIndex literal literalIndex nextSlice := by
  let literalInput : FinalCarrierTaggedLiteralInput
      source taggedLink clauseIndex literal literalIndex :=
    { linkInput := input
      literalMember := literalMember }
  exact literalInput.occurrence.publicDirections nextSlice

end PeriodicEightOccurrenceSplit
end LeanTrominoes
