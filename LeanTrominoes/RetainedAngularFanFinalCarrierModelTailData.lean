/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedDirectionData
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedLiteralData
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Named semantic model tails of final carrier literals -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Semantic occurrence slot of either named normalized carrier literal. -/
def finalCarrierSemanticOccurrenceSlotAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (literalIndex : Fin 2) : RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot
    (PeriodicThreeSATThree.formula source)
    (finalCarrierNormalizedLiteralAt
      (PeriodicThreeSATThree.formula source) taggedLink literalIndex)
    clauseIndex literalIndex

/-- Compiler-model tail selected by that semantic occurrence slot. -/
def finalCarrierModelTailAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (nextSlice : Bool)
    (literalIndex : Fin 2) : List AxisDirection :=
  (finalCarrierModelDirectionWord source taggedLink nextSlice literalIndex
    (finalCarrierSemanticOccurrenceSlotAt source taggedLink clauseIndex
      literalIndex)).tail

end PeriodicEightOccurrenceSplit
end LeanTrominoes
