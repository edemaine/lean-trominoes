/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSymmetryCertificates

/-! # Composition and inversion of all cube symmetries

Actions are determined by the three coordinate basis vectors. The finite
closure certificate checks those vectors; linearity extends it to every voxel.
-/

namespace LeanTrominoes

namespace Voxel

def scale (k : Int) (c : Voxel) : Voxel := (Cell.scale k c.1, k * c.2)

theorem basis_expansion (c : Voxel) :
    c = add (scale c.1.1 (basis 0))
      (add (scale c.1.2 (basis 1)) (scale c.2 (basis 2))) := by
  simp [add, scale, basis, Cell.add, Cell.scale]

end Voxel

namespace CubeSymmetry

theorem act_add (s : CubeSymmetry) (a b : Voxel) :
    s.act (Voxel.add a b) = Voxel.add (s.act a) (s.act b) := by
  rcases s with ⟨p, f, axis⟩
  fin_cases axis <;> cases p <;> cases f <;>
    simp [act, cycle, SquareSymmetry.act, Voxel.add, Cell.add, neg_add, add_comm]

theorem act_scale (s : CubeSymmetry) (k : Int) (c : Voxel) :
    s.act (Voxel.scale k c) = Voxel.scale k (s.act c) := by
  rcases s with ⟨p, f, axis⟩
  fin_cases axis <;> cases p <;> cases f <;>
    simp [act, cycle, SquareSymmetry.act, Voxel.scale, Cell.scale, Int.mul_neg]

theorem act_basis_expansion (s : CubeSymmetry) (c : Voxel) :
    s.act c = Voxel.add (Voxel.scale c.1.1 (s.act (Voxel.basis 0)))
      (Voxel.add (Voxel.scale c.1.2 (s.act (Voxel.basis 1)))
        (Voxel.scale c.2 (s.act (Voxel.basis 2)))) := by
  conv_lhs => rw [Voxel.basis_expansion c]
  rw [act_add, act_add, act_scale, act_scale, act_scale]

noncomputable def comp (s t : CubeSymmetry) : CubeSymmetry :=
  Classical.choose (composition_basis_certificate s t)

theorem comp_act (s t : CubeSymmetry) (c : Voxel) :
    (comp s t).act c = s.act (t.act c) := by
  have h := Classical.choose_spec (composition_basis_certificate s t)
  rw [act_basis_expansion (comp s t), act_basis_expansion t c,
    act_add, act_add, act_scale, act_scale, act_scale]
  simp only [comp, h]

noncomputable def inverse (s : CubeSymmetry) : CubeSymmetry :=
  Classical.choose (inverse_basis_certificate s)

theorem inverse_act (s : CubeSymmetry) (c : Voxel) :
    s.inverse.act c = s.inverseAct c := by
  apply s.act_injective
  rw [act_inverse_act]
  have h := Classical.choose_spec (inverse_basis_certificate s)
  rw [act_basis_expansion s.inverse c, act_add, act_add,
    act_scale, act_scale, act_scale]
  simp only [inverse, h, act_inverse_act]
  exact (Voxel.basis_expansion c).symm

theorem ext_act {s t : CubeSymmetry} (h : ∀ c, s.act c = t.act c) : s = t :=
  basis_injective_certificate s t (fun i => h (Voxel.basis i))

@[simp] theorem comp_identity (s : CubeSymmetry) : s.comp identity = s := by
  apply ext_act
  intro c
  simp [comp_act]

@[simp] theorem identity_comp (s : CubeSymmetry) : identity.comp s = s := by
  apply ext_act
  intro c
  simp [comp_act]

theorem inverse_comp_cancel (s t : CubeSymmetry) : s.inverse.comp (s.comp t) = t := by
  apply ext_act
  intro c
  simp [comp_act, inverse_act]

theorem comp_inverse_cancel (s t : CubeSymmetry) : s.comp (s.inverse.comp t) = t := by
  apply ext_act
  intro c
  simp [comp_act, inverse_act]

theorem comp_assoc (s t u : CubeSymmetry) : (s.comp t).comp u = s.comp (t.comp u) := by
  apply ext_act
  intro c
  simp only [comp_act]

end CubeSymmetry
end LeanTrominoes
