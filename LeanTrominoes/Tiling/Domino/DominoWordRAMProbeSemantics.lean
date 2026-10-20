/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMFreshCall
import LeanTrominoes.Tiling.Domino.DominoWordRAMPaddedGraph

/-! # Connecting executed coordinate tests to the original candidate graph -/
namespace LeanTrominoes.Domino.WordRAM
open Binary
variable {n d : ℕ}

theorem rawNumerator_native (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d) :
    (Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)=
      B.basis.adjugate.mulVec (B.origin u+unit direction-B.origin v) coordinate := by
  rw [rawNumerator_eval]
  congr 2
  funext j
  by_cases same : j=direction <;> simp [unit,same] <;> ring

theorem active_iff_rawNumerators (B : BasisData n d) (nonzero : B.basis.det≠0)
    (u v : Fin n) (direction : Fin d) :
    PaddedGraph.Active B u direction v ↔ ∀ coordinate,
      B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v) := by
  rw [PaddedGraph.active_iff_divisible B nonzero]
  simp only [rawNumerator_native]

theorem rawNumerator_quotient (B : BasisData n d) (nonzero : B.basis.det≠0)
    (u v : Fin n) (direction coordinate : Fin d) (active : PaddedGraph.Active B u direction v) :
    (Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det=
      PaddedGraph.coordinates B u direction v coordinate := by
  have realizes : B.basis.mulVec (PaddedGraph.coordinates B u direction v)=B.origin u+unit direction-B.origin v := by
    change B.origin v+B.basis.mulVec (PaddedGraph.coordinates B u direction v)=B.origin u+unit direction at active
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using active
  rw [rawNumerator_native,←realizes]
  simp only [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,
    Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,Int.mul_ediv_cancel_left _ nonzero]

theorem rawNumerator_parity (B : BasisData n d) (nonzero : B.basis.det≠0)
    (u v : Fin n) (direction coordinate : Fin d) (active : PaddedGraph.Active B u direction v) (bit : ℕ)
    (computed : ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det)%2=(bit : ℤ)) :
    bit=(PaddedGraph.coordinates B u direction v coordinate%2).toNat := by
  rw [rawNumerator_quotient B nonzero u v direction coordinate active] at computed
  have equal := congrArg Int.toNat computed
  simpa only [Int.toNat_natCast] using equal.symm

end LeanTrominoes.Domino.WordRAM
