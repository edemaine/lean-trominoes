/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputData
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralOccurrenceConstructor

/-! # Recovering occurrences from tagged final-carrier literal evidence -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Package complete tagged-literal evidence as the corresponding matched
final retained-carrier occurrence. -/
noncomputable def FinalCarrierTaggedLiteralInput.occurrence
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Fin 2}
    (input : FinalCarrierTaggedLiteralInput source taggedLink clauseIndex
      literal literalIndex) :
    FinalCarrierTaggedLiteralOccurrence source taggedLink clauseIndex
      literal literalIndex :=
  FinalCarrierTaggedLiteralOccurrence.ofTaggedLinkLiteral
    source
    input.linkInput.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
    input.linkInput.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
    input.linkInput.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty
    input.linkInput.sourceInput.sourceFacts.positiveOffsets
    taggedLink clauseIndex input.linkInput.taggedLinkIndexed
    literal literalIndex input.literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
