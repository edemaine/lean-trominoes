/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedRouteDirections
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralDirectionData

/-! # Public directions of tagged final retained-carrier literals -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Unpackaged parameters of an indexed carrier occurrence expose the same
exact public normalized direction word as its finite carrier model. -/
theorem FinalCarrierIndexedOccurrence.taggedLiteralPublicDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) :
    FinalCarrierTaggedLiteralPublicDirections occurrence.source
      occurrence.taggedLink occurrence.clauseIndex occurrence.literal
      occurrence.literalIndex nextSlice := by
  constructor
  exact (occurrence.publicDirections nextSlice).directions

end PeriodicEightOccurrenceSplit
end LeanTrominoes
