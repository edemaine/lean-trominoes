/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ThreeSAT.FiniteThreeSATThree
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeCNFWidthThreeIdentity
import LeanTrominoes.Tiling.Tromino.Strip.Source.PeriodicCNFStripSourceFormula

/-! # Finite sources stay finite through the strip compiler's syntax guards -/
namespace LeanTrominoes.FiniteCNF

theorem zeroOffsets_threeCNF_of_widthThree {V : Type*} (source : PeriodicCNF V)
    (width : source.WidthAtMost 3) (zero : ZeroOffsets source) :
    ZeroOffsets (PeriodicThreeCNF.formula source) := by
  rw [PeriodicThreeCNF.formula_eq_liftFormula_of_widthAtMostThree source width]
  intro clause member literal hl
  obtain ⟨originalClause,originalClauseMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨originalLiteral,originalLiteralMember,rfl⟩ := List.mem_map.mp hl
  exact zero originalClause originalClauseMember originalLiteral originalLiteralMember
end LeanTrominoes.FiniteCNF

namespace LeanTrominoes.PeriodicCNFStripReduction
attribute [local instance] variableDecidableEq variableBEq

theorem normalizedFormula_zeroOffsets (source : PeriodicCNF Nat)
    (width : source.WidthAtMost 3) (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (normalizedFormula source) :=
  FiniteThreeSATThree.formula_zero _ (FiniteCNF.zeroOffsets_threeCNF_of_widthThree source width zero)

theorem fallbackFormula_zeroOffsets : FiniteCNF.ZeroOffsets fallbackFormula := by
  intro clause member literal hl
  simp only [fallbackFormula,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> simp only [List.mem_singleton] at hl <;> subst literal <;> rfl

theorem sourceFormula_zeroOffsets (source : PeriodicCNF Nat)
    (width : source.WidthAtMost 3) (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (sourceFormula source) := by
  unfold sourceFormula
  split
  · exact normalizedFormula_zeroOffsets source width zero
  · exact fallbackFormula_zeroOffsets
end LeanTrominoes.PeriodicCNFStripReduction
