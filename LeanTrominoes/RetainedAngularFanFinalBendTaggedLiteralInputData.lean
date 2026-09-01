/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendNormalizedLiteralData
import LeanTrominoes.RetainedAngularFanFinalBendLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputData

/-! # Evidence selecting a tagged final retained-bend literal -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalBendTaggedLiteralInputThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Final bends use the same local width-three source hypotheses as final
carriers. -/
abbrev FinalBendSourceInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  FinalCarrierSourceInput source

/-- Add the global index of one tagged final retained bend. -/
structure FinalBendTaggedBendInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat) where
  sourceInput : FinalBendSourceInput source
  taggedBendIndexed :
    finalBendTaggedBendIndexed source taggedBend clauseIndex

/-- Add selection of one literal from the indexed bend implication. -/
structure FinalBendTaggedLiteralInput
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2) where
  bendInput : FinalBendTaggedBendInput source taggedBend clauseIndex
  literalMember :
    (literal, literalIndex.val) ∈
      (normalizedBendClauseAt
        (PeriodicThreeSATThree.formula source) taggedBend).zipIdx

end PeriodicEightOccurrenceSplit
end LeanTrominoes
