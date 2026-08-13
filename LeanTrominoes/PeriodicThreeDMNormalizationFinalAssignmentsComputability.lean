/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteAssignmentComputability

/-!
# Computability of complete normalized cell assignments

This module enumerates the final contracted vertices and normalized edge
interiors, preserving the compiler's vertex-first lookup priority.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem finalCellAssignments_primrec :
    Primrec finalCellAssignments :=
  (Primrec.list_append.comp finalVertexAssignments_primrec
    finalRouteAssignments_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
