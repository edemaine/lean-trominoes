/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMPlanarLineMembership
import LeanTrominoes.PeriodicThreeDMLineHardness

/-! # Native PSPACE completeness for local planar 1D colored degree-2-or-3 3DM

The input includes the complete supplied drawing, including every route point,
encoded in binary. The upper bound verifies that drawing as part of its decision.
-/
namespace LeanTrominoes.PeriodicThreeDM

theorem localPlanarLineProblem_PSPACEComplete :
    Complexity.PSPACEComplete FlatEncoding.Planar.finEncoding LocalPlanarLineProblem :=
  ⟨localPlanarLineProblem_inPSPACE,localPlanarLineProblem_PSPACEHard⟩

end LeanTrominoes.PeriodicThreeDM
