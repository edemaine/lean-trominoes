/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationCompiler

/-! # Padded terminal carrier-key axis values -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Fixed horizontal/vertical bits aligned with both classification copies
of one segment's terminal-key recipe block. -/
def Segment.terminalCarrierKeyRecipeAxes
    (segmentIndex : Nat) (segment : Segment) : List Bool :=
  let count := (segment.terminalCarrierKeyRecipeBlock segmentIndex).length
  List.replicate count true ++ List.replicate count false

/-- The two individual horizontal/vertical axis blocks of one segment. -/
def Segment.terminalCarrierKeyRecipeAxisBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List Bool) :=
  let count := (segment.terminalCarrierKeyRecipeBlock segmentIndex).length
  [List.replicate count true, List.replicate count false]

/-- Terminal axis blocks aligned with one route shape's recipe blocks. -/
def RouteShape.terminalCarrierKeyRecipeAxisBlocks
    (shape : RouteShape) : List (List Bool) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalCarrierKeyRecipeAxisBlocks tagged.2

/-- Complete fixed terminal axis-block family. -/
def terminalCarrierKeyRecipeAxisBlocks : List (List Bool) :=
  allRouteShapes.flatMap RouteShape.terminalCarrierKeyRecipeAxisBlocks

/-- Fixed axis bits aligned with every flattened terminal carrier-key recipe. -/
def terminalCarrierKeyRecipeAxes : List Bool :=
  terminalCarrierKeyRecipeAxisBlocks.flatten

/-- One zero-or-one axis value for every padded terminal candidate slot. -/
def terminalCarrierKeyAxisValues
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  FixedAxisUnaryFields.values terminalCarrierKeyRecipeAxes
    (terminalCarrierKeyExpandedActives tokens)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
