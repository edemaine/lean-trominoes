/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalBodyBlockSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceTripleOrder
import LeanTrominoes.PeriodicCNFStripGroupedVariableRoutedIncidenceOffsetSemantics

/-! # Typed shape of one local grouped variable-incidence block -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Typed occurrence bodies with an abstract routed suffix for each color. -/
def groupedVariableIncidenceTypedShapeBodies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (routedBody : WireColor → List AxisDirection) :
    List (List AxisDirection) :=
  (occurrenceTriples source atom slot).flatMap fun triple =>
    incidenceColors.map fun color =>
      HorizontalFiniteIncidenceDirectionQuery.directions
          (.variable fan (variableSiteTripleOfTyped triple) color) ++
        if triple = routedOccurrenceTriple source atom slot color then
          routedBody color
        else []

end LeanTrominoes.PeriodicCNFStripReduction

end
