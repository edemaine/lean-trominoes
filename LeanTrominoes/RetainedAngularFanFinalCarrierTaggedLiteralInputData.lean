/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup
import LeanTrominoes.RetainedAngularFanFinalCarrierSourceFacts
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkData

/-! # Evidence selecting a tagged final retained-carrier literal -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierTaggedLiteralInputThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Packaged source-shape evidence for final retained-carrier semantics. -/
structure FinalCarrierSourceInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) where
  sourceFacts : FinalCarrierSourceFacts source

/-- Add the global index of one tagged final retained-carrier link. -/
structure FinalCarrierTaggedLinkInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat) where
  sourceInput : FinalCarrierSourceInput source
  taggedLinkIndexed :
    finalCarrierTaggedLinkIndexed source taggedLink clauseIndex

/-- Add selection of one literal from the indexed carrier implication,
completing the evidence needed to recover its positioned occurrence. -/
structure FinalCarrierTaggedLiteralInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2) where
  linkInput : FinalCarrierTaggedLinkInput source taggedLink clauseIndex
  literalMember :
    (literal, literalIndex.val) ∈
      (normalizedCarrierClauseAt
        (PeriodicThreeSATThree.formula source) taggedLink).zipIdx

end PeriodicEightOccurrenceSplit
end LeanTrominoes
