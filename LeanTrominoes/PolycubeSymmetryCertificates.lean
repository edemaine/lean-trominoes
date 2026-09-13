/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeBasic

/-! # Finite certificates for composition and inversion of cube symmetries -/

namespace LeanTrominoes
namespace Voxel

def basis : Fin 3 → Voxel
  | 0 => ((1, 0), 0)
  | 1 => ((0, 1), 0)
  | 2 => ((0, 0), 1)

end Voxel

namespace CubeSymmetry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem composition_basis_certificate : ∀ s t : CubeSymmetry, ∃ u : CubeSymmetry,
    ∀ i : Fin 3, u.act (Voxel.basis i) = s.act (t.act (Voxel.basis i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem inverse_basis_certificate : ∀ s : CubeSymmetry, ∃ t : CubeSymmetry,
    ∀ i : Fin 3, t.act (Voxel.basis i) = s.inverseAct (Voxel.basis i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem basis_injective_certificate : ∀ s t : CubeSymmetry,
    (∀ i : Fin 3, s.act (Voxel.basis i) = t.act (Voxel.basis i)) → s = t := by
  decide +kernel

end CubeSymmetry
end LeanTrominoes
