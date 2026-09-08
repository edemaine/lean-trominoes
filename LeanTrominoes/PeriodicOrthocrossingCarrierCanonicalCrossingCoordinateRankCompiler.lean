/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedValueCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingMacroOriginCompiler

/-! # Canonical crossing coordinates in the physical dictionary order -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
open Computability Turing CarrierCrossingPointField

def rankedValues (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRankOrderedValues.values (values offset field) descriptors

noncomputable def rankedValuesComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime CarrierSourceKeyRankOrderedValues.descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields (rankedValues offset field) :=
  CarrierSourceKeyRankOrderedValues.valuesComputableInPolyTime (values offset field)
    (valuesWithSentinel_length offset field) (valuesWithSentinelComputableInPolyTime offset field)

/-- Canonical coordinate columns and physical key words use the same global carrier enumeration. -/
theorem rankedValues_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable] (offset : CrossingSide → Cell) (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    rankedValues offset field (PeriodicCNF.numericRouteDescriptors formula) =
      (CarrierCrossingMacroOrigin.nodes (PeriodicCNF.numericRouteDescriptors formula)).map
        (nodeValue offset field (routeDescriptorStreamGridSize (PeriodicCNF.numericRouteDescriptors formula))) := by
  rw [rankedValues, CarrierSourceKeyRankOrderedValues.values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty (values offset field)
    (nodeValue offset field (routeDescriptorStreamGridSize (PeriodicCNF.numericRouteDescriptors formula)))
    (values_forall₂ offset field _ _ (numericRouteDescriptors_gridSize_eq_stream formula nonempty))]
  simp only [CarrierCrossingMacroOrigin.nodes, List.map_map, Function.comp_def]

/-- Side-local offsets give precisely the gauged boundary placement. -/
theorem boundary_nodePoint_eq_position {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (boundary : CrossingBoundary) :
    nodePoint CrossingSide.localPosition (drawingGridSize formula.incidenceGraph) (.boundary boundary) =
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position ⟨.boundary boundary⟩ := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_macrocell]
  rfl

/-- For an internal role, the same canonical crossing point receives that role's local offset. -/
theorem internal_nodePoint_eq_position {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (crossing : CrossingRecord)
    (role : PlanarThreeSAT.CrossoverInternal) :
    nodePoint (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role))
        (drawingGridSize formula.incidenceGraph) (.boundary ⟨crossing, .left⟩) =
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨.crossoverInternal (crossing, role)⟩ := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_macrocell]
  rfl

end LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
end
