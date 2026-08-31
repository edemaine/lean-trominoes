/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence

/-! # Direction claims for tagged final retained-carrier literals -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The explicit public normalized direction claim for a tagged final
retained-carrier literal. -/
structure FinalCarrierTaggedLiteralPublicDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2)
    (nextSlice : Bool) : Prop where
  directions :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          (PeriodicThreeSATThree.formula source) clauseIndex literalIndex) =
      finalCarrierModelDirectionWord source taggedLink nextSlice literalIndex
        (retainedFinalCoordinatedOccurrenceSlot
          (PeriodicThreeSATThree.formula source)
          literal clauseIndex literalIndex)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

