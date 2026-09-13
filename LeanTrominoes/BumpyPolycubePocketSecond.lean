/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubePocketData

/-! # Kernel-checked pocket certificates, separated to bound reduction memory -/
namespace LeanTrominoes.Polycube.BumpyPocket
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem second_identity_false_0 :
    SecondCertificate ⟨.identity, false, 0⟩ := by decide +kernel

theorem second_identity_false_1 :
    SecondCertificate ⟨.identity, false, 1⟩ := by decide +kernel

theorem second_identity_false_2 :
    SecondCertificate ⟨.identity, false, 2⟩ := by decide +kernel

theorem second_identity_true_0 :
    SecondCertificate ⟨.identity, true, 0⟩ := by decide +kernel

theorem second_identity_true_1 :
    SecondCertificate ⟨.identity, true, 1⟩ := by decide +kernel

theorem second_identity_true_2 :
    SecondCertificate ⟨.identity, true, 2⟩ := by decide +kernel

theorem second_rotate90_false_0 :
    SecondCertificate ⟨.rotate90, false, 0⟩ := by decide +kernel

theorem second_rotate90_false_1 :
    SecondCertificate ⟨.rotate90, false, 1⟩ := by decide +kernel

theorem second_rotate90_false_2 :
    SecondCertificate ⟨.rotate90, false, 2⟩ := by decide +kernel

theorem second_rotate90_true_0 :
    SecondCertificate ⟨.rotate90, true, 0⟩ := by decide +kernel

theorem second_rotate90_true_1 :
    SecondCertificate ⟨.rotate90, true, 1⟩ := by decide +kernel

theorem second_rotate90_true_2 :
    SecondCertificate ⟨.rotate90, true, 2⟩ := by decide +kernel

theorem second_rotate180_false_0 :
    SecondCertificate ⟨.rotate180, false, 0⟩ := by decide +kernel

theorem second_rotate180_false_1 :
    SecondCertificate ⟨.rotate180, false, 1⟩ := by decide +kernel

theorem second_rotate180_false_2 :
    SecondCertificate ⟨.rotate180, false, 2⟩ := by decide +kernel

theorem second_rotate180_true_0 :
    SecondCertificate ⟨.rotate180, true, 0⟩ := by decide +kernel

theorem second_rotate180_true_1 :
    SecondCertificate ⟨.rotate180, true, 1⟩ := by decide +kernel

theorem second_rotate180_true_2 :
    SecondCertificate ⟨.rotate180, true, 2⟩ := by decide +kernel

theorem second_rotate270_false_0 :
    SecondCertificate ⟨.rotate270, false, 0⟩ := by decide +kernel

theorem second_rotate270_false_1 :
    SecondCertificate ⟨.rotate270, false, 1⟩ := by decide +kernel

theorem second_rotate270_false_2 :
    SecondCertificate ⟨.rotate270, false, 2⟩ := by decide +kernel

theorem second_rotate270_true_0 :
    SecondCertificate ⟨.rotate270, true, 0⟩ := by decide +kernel

theorem second_rotate270_true_1 :
    SecondCertificate ⟨.rotate270, true, 1⟩ := by decide +kernel

theorem second_rotate270_true_2 :
    SecondCertificate ⟨.rotate270, true, 2⟩ := by decide +kernel

theorem second_reflectX_false_0 :
    SecondCertificate ⟨.reflectX, false, 0⟩ := by decide +kernel

theorem second_reflectX_false_1 :
    SecondCertificate ⟨.reflectX, false, 1⟩ := by decide +kernel

theorem second_reflectX_false_2 :
    SecondCertificate ⟨.reflectX, false, 2⟩ := by decide +kernel

theorem second_reflectX_true_0 :
    SecondCertificate ⟨.reflectX, true, 0⟩ := by decide +kernel

theorem second_reflectX_true_1 :
    SecondCertificate ⟨.reflectX, true, 1⟩ := by decide +kernel

theorem second_reflectX_true_2 :
    SecondCertificate ⟨.reflectX, true, 2⟩ := by decide +kernel

theorem second_reflectDiagonal_false_0 :
    SecondCertificate ⟨.reflectDiagonal, false, 0⟩ := by decide +kernel

theorem second_reflectDiagonal_false_1 :
    SecondCertificate ⟨.reflectDiagonal, false, 1⟩ := by decide +kernel

theorem second_reflectDiagonal_false_2 :
    SecondCertificate ⟨.reflectDiagonal, false, 2⟩ := by decide +kernel

theorem second_reflectDiagonal_true_0 :
    SecondCertificate ⟨.reflectDiagonal, true, 0⟩ := by decide +kernel

theorem second_reflectDiagonal_true_1 :
    SecondCertificate ⟨.reflectDiagonal, true, 1⟩ := by decide +kernel

theorem second_reflectDiagonal_true_2 :
    SecondCertificate ⟨.reflectDiagonal, true, 2⟩ := by decide +kernel

theorem second_reflectY_false_0 :
    SecondCertificate ⟨.reflectY, false, 0⟩ := by decide +kernel

theorem second_reflectY_false_1 :
    SecondCertificate ⟨.reflectY, false, 1⟩ := by decide +kernel

theorem second_reflectY_false_2 :
    SecondCertificate ⟨.reflectY, false, 2⟩ := by decide +kernel

theorem second_reflectY_true_0 :
    SecondCertificate ⟨.reflectY, true, 0⟩ := by decide +kernel

theorem second_reflectY_true_1 :
    SecondCertificate ⟨.reflectY, true, 1⟩ := by decide +kernel

theorem second_reflectY_true_2 :
    SecondCertificate ⟨.reflectY, true, 2⟩ := by decide +kernel

theorem second_reflectAntidiagonal_false_0 :
    SecondCertificate ⟨.reflectAntidiagonal, false, 0⟩ := by decide +kernel

theorem second_reflectAntidiagonal_false_1 :
    SecondCertificate ⟨.reflectAntidiagonal, false, 1⟩ := by decide +kernel

theorem second_reflectAntidiagonal_false_2 :
    SecondCertificate ⟨.reflectAntidiagonal, false, 2⟩ := by decide +kernel

theorem second_reflectAntidiagonal_true_0 :
    SecondCertificate ⟨.reflectAntidiagonal, true, 0⟩ := by decide +kernel

theorem second_reflectAntidiagonal_true_1 :
    SecondCertificate ⟨.reflectAntidiagonal, true, 1⟩ := by decide +kernel

theorem second_reflectAntidiagonal_true_2 :
    SecondCertificate ⟨.reflectAntidiagonal, true, 2⟩ := by decide +kernel

theorem second_source_certificate (s : CubeSymmetry) : SecondCertificate s := by
  rcases s with ⟨s, flip, axis⟩
  cases s <;> cases flip <;> fin_cases axis
  · exact second_identity_false_0
  · exact second_identity_false_1
  · exact second_identity_false_2
  · exact second_identity_true_0
  · exact second_identity_true_1
  · exact second_identity_true_2
  · exact second_rotate90_false_0
  · exact second_rotate90_false_1
  · exact second_rotate90_false_2
  · exact second_rotate90_true_0
  · exact second_rotate90_true_1
  · exact second_rotate90_true_2
  · exact second_rotate180_false_0
  · exact second_rotate180_false_1
  · exact second_rotate180_false_2
  · exact second_rotate180_true_0
  · exact second_rotate180_true_1
  · exact second_rotate180_true_2
  · exact second_rotate270_false_0
  · exact second_rotate270_false_1
  · exact second_rotate270_false_2
  · exact second_rotate270_true_0
  · exact second_rotate270_true_1
  · exact second_rotate270_true_2
  · exact second_reflectX_false_0
  · exact second_reflectX_false_1
  · exact second_reflectX_false_2
  · exact second_reflectX_true_0
  · exact second_reflectX_true_1
  · exact second_reflectX_true_2
  · exact second_reflectDiagonal_false_0
  · exact second_reflectDiagonal_false_1
  · exact second_reflectDiagonal_false_2
  · exact second_reflectDiagonal_true_0
  · exact second_reflectDiagonal_true_1
  · exact second_reflectDiagonal_true_2
  · exact second_reflectY_false_0
  · exact second_reflectY_false_1
  · exact second_reflectY_false_2
  · exact second_reflectY_true_0
  · exact second_reflectY_true_1
  · exact second_reflectY_true_2
  · exact second_reflectAntidiagonal_false_0
  · exact second_reflectAntidiagonal_false_1
  · exact second_reflectAntidiagonal_false_2
  · exact second_reflectAntidiagonal_true_0
  · exact second_reflectAntidiagonal_true_1
  · exact second_reflectAntidiagonal_true_2

end LeanTrominoes.Polycube.BumpyPocket
