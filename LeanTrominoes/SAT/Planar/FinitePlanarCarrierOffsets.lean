/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FiniteOrthocrossingCrossings
import LeanTrominoes.SAT.CNF.FiniteCNFIncidenceOffsets
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedFormula
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarPeriodicization

/-! # Retained planar carriers of finite sources have consistent offsets -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT
variable {V : Type*} [DecidableEq V] (formula : PeriodicCNF V)

def planarNodeOffset (node : PlanarSATNode V) : Cell :=
  (normalizePlanarSATVariable formula (.inl node)).2

theorem retainedCarrierNode_offset_eq_translate
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula)
    (node : CarrierNode) (member : node∈retainedDrawingCarrierNodes formula.incidenceGraph) :
    planarNodeOffset formula (.carrier node)=node.carrierKey.2.2 := by
  cases node with
  | terminal terminal => rfl
  | boundary boundary =>
    have boundaryMem : boundary∈retainedCrossingBoundaries formula.incidenceGraph := by
      simpa [retainedDrawingCarrierNodes] using member
    have offsets := retainedCrossings_translates_eq_periodShift wellFormed degree
      (FiniteCNF.incidenceGraph_zero formula zero) (retainedCrossingBoundary_crossing_mem _ boundaryMem)
    cases sideEq : boundary.side <;>
      simp only [planarNodeOffset,normalizePlanarSATVariable,CarrierNode.carrierKey,
        CrossingBoundary.carrierKey,PeriodicGridDrawing.SegmentOccurrenceKey,sideEq] <;>
      first | exact offsets.1.symm | exact offsets.2.symm

theorem retainedCarrierLink_offsets_equal
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula)
    {link : EqualityLink CarrierNode} (member : link∈retainedDrawingCompleteCarrierLinks formula.incidenceGraph) :
    planarNodeOffset formula (.carrier link.first)=planarNodeOffset formula (.carrier link.second) := by
  have endpoints := retainedDrawingCompleteCarrierLink_endpoints_mem formula.incidenceGraph member
  rw [retainedCarrierNode_offset_eq_translate formula wellFormed degree zero link.first endpoints.1,
    retainedCarrierNode_offset_eq_translate formula wellFormed degree zero link.second endpoints.2]
  exact congrArg (fun key : Nat×Nat×Cell => key.2.2)
    (retainedDrawingCompleteCarrierLinks_common_key formula.incidenceGraph member)

end LeanTrominoes.PeriodicOrthocrossing
