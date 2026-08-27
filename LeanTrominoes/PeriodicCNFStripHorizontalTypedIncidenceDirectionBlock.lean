/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalFixedRedTypedIncidenceDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOrdinaryTypedIncidenceDirectionBlock

/-! # Compact direction blocks for all horizontal typed incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A complete typed incidence word is either a compact variable-incidence
block or one entry from the finite clause-core table. -/
inductive HorizontalTypedIncidenceDirectionBlock where
  | variable
      (input : HorizontalVariableTypedIncidenceRouteInput)
      (block : HorizontalVariableTypedIncidenceDirectionBlock)
  | clause (input : X3CClauseSet × WireColor)

/-- Interpret one compact complete typed-incidence block. -/
def HorizontalTypedIncidenceDirectionBlock.directions :
    HorizontalTypedIncidenceDirectionBlock → List AxisDirection
  | .variable input block =>
      horizontalVariableTypedIncidenceDirections input block
  | .clause input => horizontalClauseIncidenceDirections input

/-- Every genuine typed incidence has one compact complete direction block. -/
theorem horizontalTypedIncidenceRoute_directionBlock_of_mem
    (source : PeriodicCNF Nat)
    (triple : Triple RoutedVariable)
    (member : triple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    ∃ block : HorizontalTypedIncidenceDirectionBlock,
      unitSubdivisionDirections
          (horizontalTypedIncidenceRouteComputed
            ((source, triple), color)) =
        block.directions := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      rcases horizontalOrdinaryVariableTypedIncidenceRoute_directionBlock
          source atom slot variant localTriple member color with
        ⟨block, directions⟩
      refine ⟨.variable
        ((((source, atom), slot),
          Triple.ordinary atom slot variant localTriple), color)
        block, ?_⟩
      simpa only [horizontalTypedIncidenceRouteComputed,
        HorizontalTypedIncidenceDirectionBlock.directions] using directions
  | fixedRed atom slot localTriple =>
      rcases horizontalFixedRedVariableTypedIncidenceRoute_directionBlock
          source atom slot localTriple member color with
        ⟨block, directions⟩
      refine ⟨.variable
        ((((source, atom), slot),
          Triple.fixedRed atom slot localTriple), color)
        block, ?_⟩
      simpa only [horizontalTypedIncidenceRouteComputed,
        HorizontalTypedIncidenceDirectionBlock.directions] using directions
  | clause clauseIndex set =>
      refine ⟨.clause (set, color), ?_⟩
      simpa only [horizontalTypedIncidenceRouteComputed,
        HorizontalTypedIncidenceDirectionBlock.directions] using
        unitSubdivisionDirections_horizontalClauseIncidenceRouteComputed
          (((source, clauseIndex), set), color)

end PeriodicCNFStripReduction
end LeanTrominoes

end
