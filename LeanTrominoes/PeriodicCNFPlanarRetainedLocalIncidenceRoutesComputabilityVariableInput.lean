/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityDuplicatorTables

/-! # Runtime input type for one retained variable route -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

abbrev RoutedVariableRouteInput (Variable : Type*) :=
  (((PeriodicCNF Variable × VariableRouteSite Variable) ×
    DuplicatorArm) × Nat) × Nat

end PeriodicOrthocrossing
end LeanTrominoes
