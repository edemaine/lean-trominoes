/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity
import LeanTrominoes.PolycubeTiling
import Mathlib.Tactic.FinCases

/-! # Two occupied planes confine any connected placement meeting the middle -/

namespace LeanTrominoes

theorem CubeSymmetry.adjacent_height (s : CubeSymmetry) (a b : Voxel)
    (adjacent : Voxel.FaceAdjacent a b) :
    (s.act a).2 - 1 ≤ (s.act b).2 ∧ (s.act b).2 ≤ (s.act a).2 + 1 := by
  simp only [Voxel.FaceAdjacent,Cell.SideAdjacent,Prod.ext_iff] at adjacent
  have hx : a.1.1 - 1 ≤ b.1.1 ∧ b.1.1 ≤ a.1.1 + 1 := by omega
  have hy : a.1.2 - 1 ≤ b.1.2 ∧ b.1.2 ≤ a.1.2 + 1 := by omega
  have hz : a.2 - 1 ≤ b.2 ∧ b.2 ≤ a.2 + 1 := by omega
  have negBounds {x y : Int} (h : x - 1 ≤ y ∧ y ≤ x + 1) :
      -x - 1 ≤ -y ∧ -y ≤ -x + 1 := by omega
  rcases s with ⟨planar,flip,axis⟩
  fin_cases axis <;> cases planar <;> cases flip <;>
    simp only [CubeSymmetry.act,CubeSymmetry.cycle,SquareSymmetry.act,
      Equiv.coe_fn_mk,Equiv.refl_apply,Bool.false_eq_true,ite_false,ite_true] <;> first | exact hx | exact hy | exact hz | exact negBounds hx | exact negBounds hy | exact negBounds hz

theorem VoxelPlacement.confined_by_caps {ι : Type*} (tiles : ι → Polycube)
    (p : VoxelPlacement ι) (connected : (tiles p.kind).IsConnected)
    (avoids : ∀ c ∈ p.cells tiles, c.2 ≠ -1 ∧ c.2 ≠ 3)
    (a : Voxel) (ha : a ∈ p.cells tiles) (middle : 0 ≤ a.2 ∧ a.2 ≤ 2) :
    ∀ c ∈ p.cells tiles, 0 ≤ c.2 ∧ c.2 ≤ 2 := by
  let height (q : Voxel) := (Voxel.add p.offset (p.symmetry.act q)).2
  have absent (q : {c // c ∈ tiles p.kind}) : height q.val ≠ -1 ∧ height q.val ≠ 3 :=
    avoids _ ((p.mem_cells_iff tiles _).mpr ⟨q.val,q.property,rfl⟩)
  have invariant {u v : {c // c ∈ tiles p.kind}}
      (walk : (tiles p.kind).faceGraph.Walk u v) :
      (0 ≤ height u.val ∧ height u.val ≤ 2) → (0 ≤ height v.val ∧ height v.val ≤ 2) := by
    induction walk with
    | nil => exact id
    | @cons u v w edge walk ih =>
      intro hu
      apply ih
      have step := p.symmetry.adjacent_height u.val v.val edge
      have miss := absent v
      dsimp [height,Voxel.add] at *
      omega
  obtain ⟨q,hq,eq⟩ := (p.mem_cells_iff tiles a).mp ha
  intro c hc
  obtain ⟨r,hr,er⟩ := (p.mem_cells_iff tiles c).mp hc
  obtain ⟨walk⟩ := connected.preconnected ⟨q,hq⟩ ⟨r,hr⟩
  have start : 0 ≤ height q ∧ height q ≤ 2 := by simpa [height,eq] using middle
  simpa [height,er] using invariant walk start

end LeanTrominoes
