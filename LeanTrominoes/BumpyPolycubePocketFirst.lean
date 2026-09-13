/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubePocketData

/-! # Kernel-checked pocket certificates, separated to bound reduction memory -/
namespace LeanTrominoes.Polycube.BumpyPocket
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem first_identity_false_0 :
    FirstCertificate ⟨.identity, false, 0⟩ := by decide +kernel

theorem first_identity_false_1 :
    FirstCertificate ⟨.identity, false, 1⟩ := by decide +kernel

theorem first_identity_false_2 :
    FirstCertificate ⟨.identity, false, 2⟩ := by decide +kernel

theorem first_identity_true_0 :
    FirstCertificate ⟨.identity, true, 0⟩ := by decide +kernel

theorem first_identity_true_1 :
    FirstCertificate ⟨.identity, true, 1⟩ := by decide +kernel

theorem first_identity_true_2 :
    FirstCertificate ⟨.identity, true, 2⟩ := by decide +kernel

theorem first_rotate90_false_0 :
    FirstCertificate ⟨.rotate90, false, 0⟩ := by decide +kernel

theorem first_rotate90_false_1 :
    FirstCertificate ⟨.rotate90, false, 1⟩ := by decide +kernel

theorem first_rotate90_false_2 :
    FirstCertificate ⟨.rotate90, false, 2⟩ := by decide +kernel

theorem first_rotate90_true_0 :
    FirstCertificate ⟨.rotate90, true, 0⟩ := by decide +kernel

theorem first_rotate90_true_1 :
    FirstCertificate ⟨.rotate90, true, 1⟩ := by decide +kernel

theorem first_rotate90_true_2 :
    FirstCertificate ⟨.rotate90, true, 2⟩ := by decide +kernel

theorem first_rotate180_false_0 :
    FirstCertificate ⟨.rotate180, false, 0⟩ := by decide +kernel

theorem first_rotate180_false_1 :
    FirstCertificate ⟨.rotate180, false, 1⟩ := by decide +kernel

theorem first_rotate180_false_2 :
    FirstCertificate ⟨.rotate180, false, 2⟩ := by decide +kernel

theorem first_rotate180_true_0 :
    FirstCertificate ⟨.rotate180, true, 0⟩ := by decide +kernel

theorem first_rotate180_true_1 :
    FirstCertificate ⟨.rotate180, true, 1⟩ := by decide +kernel

theorem first_rotate180_true_2 :
    FirstCertificate ⟨.rotate180, true, 2⟩ := by decide +kernel

theorem first_rotate270_false_0 :
    FirstCertificate ⟨.rotate270, false, 0⟩ := by decide +kernel

theorem first_rotate270_false_1 :
    FirstCertificate ⟨.rotate270, false, 1⟩ := by decide +kernel

theorem first_rotate270_false_2 :
    FirstCertificate ⟨.rotate270, false, 2⟩ := by decide +kernel

theorem first_rotate270_true_0 :
    FirstCertificate ⟨.rotate270, true, 0⟩ := by decide +kernel

theorem first_rotate270_true_1 :
    FirstCertificate ⟨.rotate270, true, 1⟩ := by decide +kernel

theorem first_rotate270_true_2 :
    FirstCertificate ⟨.rotate270, true, 2⟩ := by decide +kernel

theorem first_reflectX_false_0 :
    FirstCertificate ⟨.reflectX, false, 0⟩ := by decide +kernel

theorem first_reflectX_false_1 :
    FirstCertificate ⟨.reflectX, false, 1⟩ := by decide +kernel

theorem first_reflectX_false_2 :
    FirstCertificate ⟨.reflectX, false, 2⟩ := by decide +kernel

theorem first_reflectX_true_0 :
    FirstCertificate ⟨.reflectX, true, 0⟩ := by decide +kernel

theorem first_reflectX_true_1 :
    FirstCertificate ⟨.reflectX, true, 1⟩ := by decide +kernel

theorem first_reflectX_true_2 :
    FirstCertificate ⟨.reflectX, true, 2⟩ := by decide +kernel

theorem first_reflectDiagonal_false_0 :
    FirstCertificate ⟨.reflectDiagonal, false, 0⟩ := by decide +kernel

theorem first_reflectDiagonal_false_1 :
    FirstCertificate ⟨.reflectDiagonal, false, 1⟩ := by decide +kernel

theorem first_reflectDiagonal_false_2 :
    FirstCertificate ⟨.reflectDiagonal, false, 2⟩ := by decide +kernel

theorem first_reflectDiagonal_true_0 :
    FirstCertificate ⟨.reflectDiagonal, true, 0⟩ := by decide +kernel

theorem first_reflectDiagonal_true_1 :
    FirstCertificate ⟨.reflectDiagonal, true, 1⟩ := by decide +kernel

theorem first_reflectDiagonal_true_2 :
    FirstCertificate ⟨.reflectDiagonal, true, 2⟩ := by decide +kernel

theorem first_reflectY_false_0 :
    FirstCertificate ⟨.reflectY, false, 0⟩ := by decide +kernel

theorem first_reflectY_false_1 :
    FirstCertificate ⟨.reflectY, false, 1⟩ := by decide +kernel

theorem first_reflectY_false_2 :
    FirstCertificate ⟨.reflectY, false, 2⟩ := by decide +kernel

theorem first_reflectY_true_0 :
    FirstCertificate ⟨.reflectY, true, 0⟩ := by decide +kernel

theorem first_reflectY_true_1 :
    FirstCertificate ⟨.reflectY, true, 1⟩ := by decide +kernel

theorem first_reflectY_true_2 :
    FirstCertificate ⟨.reflectY, true, 2⟩ := by decide +kernel

theorem first_reflectAntidiagonal_false_0 :
    FirstCertificate ⟨.reflectAntidiagonal, false, 0⟩ := by decide +kernel

theorem first_reflectAntidiagonal_false_1 :
    FirstCertificate ⟨.reflectAntidiagonal, false, 1⟩ := by decide +kernel

theorem first_reflectAntidiagonal_false_2 :
    FirstCertificate ⟨.reflectAntidiagonal, false, 2⟩ := by decide +kernel

theorem first_reflectAntidiagonal_true_0 :
    FirstCertificate ⟨.reflectAntidiagonal, true, 0⟩ := by decide +kernel

theorem first_reflectAntidiagonal_true_1 :
    FirstCertificate ⟨.reflectAntidiagonal, true, 1⟩ := by decide +kernel

theorem first_reflectAntidiagonal_true_2 :
    FirstCertificate ⟨.reflectAntidiagonal, true, 2⟩ := by decide +kernel

theorem first_source_certificate (s : CubeSymmetry) : FirstCertificate s := by
  rcases s with ⟨s, flip, axis⟩
  cases s <;> cases flip <;> fin_cases axis
  · exact first_identity_false_0
  · exact first_identity_false_1
  · exact first_identity_false_2
  · exact first_identity_true_0
  · exact first_identity_true_1
  · exact first_identity_true_2
  · exact first_rotate90_false_0
  · exact first_rotate90_false_1
  · exact first_rotate90_false_2
  · exact first_rotate90_true_0
  · exact first_rotate90_true_1
  · exact first_rotate90_true_2
  · exact first_rotate180_false_0
  · exact first_rotate180_false_1
  · exact first_rotate180_false_2
  · exact first_rotate180_true_0
  · exact first_rotate180_true_1
  · exact first_rotate180_true_2
  · exact first_rotate270_false_0
  · exact first_rotate270_false_1
  · exact first_rotate270_false_2
  · exact first_rotate270_true_0
  · exact first_rotate270_true_1
  · exact first_rotate270_true_2
  · exact first_reflectX_false_0
  · exact first_reflectX_false_1
  · exact first_reflectX_false_2
  · exact first_reflectX_true_0
  · exact first_reflectX_true_1
  · exact first_reflectX_true_2
  · exact first_reflectDiagonal_false_0
  · exact first_reflectDiagonal_false_1
  · exact first_reflectDiagonal_false_2
  · exact first_reflectDiagonal_true_0
  · exact first_reflectDiagonal_true_1
  · exact first_reflectDiagonal_true_2
  · exact first_reflectY_false_0
  · exact first_reflectY_false_1
  · exact first_reflectY_false_2
  · exact first_reflectY_true_0
  · exact first_reflectY_true_1
  · exact first_reflectY_true_2
  · exact first_reflectAntidiagonal_false_0
  · exact first_reflectAntidiagonal_false_1
  · exact first_reflectAntidiagonal_false_2
  · exact first_reflectAntidiagonal_true_0
  · exact first_reflectAntidiagonal_true_1
  · exact first_reflectAntidiagonal_true_2

end LeanTrominoes.Polycube.BumpyPocket
