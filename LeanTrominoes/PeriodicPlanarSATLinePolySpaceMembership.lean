/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATFullVerification

/-! # Native PSPACE upper bounds for all four planar one-dimensional SAT variants

The input supplies both the formula and its drawing. The verifier checks SAT,
locality, clause width, the applicable occurrence bound, the grid bound,
planarity, incidence counts, vertex compatibility, and every route endpoint.
-/
namespace LeanTrominoes.PeriodicPlanarSAT
open ComponentVerification

theorem ordinary_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding Orbit.LocalOneDimensionalProblem :=
  ⟨ordinary.fullDecider true 8847360 ordinary_iff_precheck_routes⟩

theorem ordinaryThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding Orbit.LocalOneDimensionalThreeOccurrenceProblem :=
  ⟨ordinaryThree.fullDecider true 8847360 ordinaryThree_iff_precheck_routes⟩

theorem exactOne_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneProblem :=
  ⟨exactOne.fullDecider false 637009920 exactOne_iff_precheck_routes⟩

theorem exactOneThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem :=
  ⟨exactOneThree.fullDecider false 637009920 exactOneThree_iff_precheck_routes⟩

end LeanTrominoes.PeriodicPlanarSAT
