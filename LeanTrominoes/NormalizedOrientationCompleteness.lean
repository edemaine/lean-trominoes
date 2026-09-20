/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationSyntax
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Co-r.e. completeness of normalized plane trichromatic orientation -/
namespace LeanTrominoes.Gadget.NormalizedOrientation

/-- Normalized plane orientation, rejecting malformed or unseparated drawings. -/
def Problem (d : Drawing) : Prop := d.VerticesSeparated ∧ d.HasOrientation

theorem problem_iff (d : Drawing) :
    Problem d ↔ Checks d ∧ PeriodicTrominoTiling .I (d.periodicRegion .I) := by
  constructor
  · rintro ⟨separated, oriented⟩
    exact ⟨(checks_iff d).2 ⟨oriented.1,separated⟩,
      (periodicRegion_correct_of_normalized .I iOrientationBehaviorCorrect d
        oriented.1 separated).1 oriented⟩
  · rintro ⟨checked, tiled⟩
    obtain ⟨wellFormed,separated⟩ := (checks_iff d).1 checked
    exact ⟨separated,(periodicRegion_correct_of_normalized .I iOrientationBehaviorCorrect d
      wellFormed separated).2 tiled⟩

def Obstruction (d : Drawing) (n : Nat) : Prop :=
  ¬ Checks d ∨ TrominoAssignment.PeriodicTrominoObstruction .I (d.periodicRegion .I,n)

theorem obstruction_primrec : PrimrecRel Obstruction :=
  (checks_primrec.comp Primrec.fst).not.or
    ((TrominoAssignment.periodicTrominoObstruction_primrec .I).comp
      (Primrec.pair ((periodicRegion_primrec .I).comp Primrec.fst) Primrec.snd))

theorem exists_obstruction_iff (d : Drawing) : (∃ n, Obstruction d n) ↔ ¬ Problem d := by
  classical
  simp only [Obstruction, exists_or, exists_const,
    TrominoAssignment.exists_periodicTrominoObstruction_iff, problem_iff, not_and_or]

theorem coRE : LeanWang.CoREPred Problem :=
  (LeanWang.REPred.exists_nat (p := Obstruction) obstruction_primrec.computablePred).of_eq
    exists_obstruction_iff

theorem coREHard : LeanWang.CoREHard Problem := by
  intro A _ source hs
  obtain ⟨r⟩ := PeriodicWangPlanarThreeDMReduction.normalizedOrientationCoREHard source hs
  refine ⟨r.drawing,r.drawing_computable,?_⟩
  intro a
  constructor
  · intro h; exact ⟨r.verticesSeparated a,(r.correct a).1 h⟩
  · intro h; exact (r.correct a).2 h.2

/-- Plane trichromatic orientation remains co-r.e. complete on the normalized
orthogonal drawings used by the tromino reduction. -/
theorem coREComplete : LeanWang.CoREComplete Problem := ⟨coRE,coREHard⟩

end LeanTrominoes.Gadget.NormalizedOrientation
