/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPatternCertificates
import LeanTrominoes.TrominoFiniteArea

namespace LeanTrominoes.CompletionPattern

theorem Pattern.residual_tileable (p : Pattern) (outside : Finset Cell)
    (completed : p.Completable outside) : p.tromino.Tileable (p.residual outside : Set Cell) := by
  have tiled := ((p.tromino.completable_iff _ _).mp completed).2
  have cells : (p.target outside : Set Cell) \
      Tromino.occupied (p.tromino.finiteFootprints p.prefill : Set (Finset Cell)) =
      (p.residual outside : Set Cell) := by
    ext c
    simp [Pattern.residual,Tromino.occupied,Tromino.finiteFootprints]
  rwa [cells] at tiled

theorem Pattern.area_dvd (p : Pattern) (outside : Finset Cell)
    (completed : p.Completable outside) : 3 ∣ (p.residual outside).card := by
  classical
  have tiled : p.tromino.Tileable ((p.residual outside).toList.toFinset : Set Cell) := by
    simpa using p.residual_tileable outside completed
  simpa using TrominoFiniteCover.card_dvd_of_tileable p.tromino _ tiled

def Pattern.rejectsWithArea (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteExclusion.Node) : Bool :=
  !decide (3 ∣ (p.residual outside).card) || p.rejects outside certificate

theorem Pattern.not_completable_of_rejectsWithArea (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteExclusion.Node)
    (rejected : p.rejectsWithArea outside certificate = true) : ¬ p.Completable outside := by
  intro completed
  have guard : decide (3 ∣ (p.residual outside).card) = true := by
    simpa only [decide_eq_true_eq] using p.area_dvd outside completed
  unfold Pattern.rejectsWithArea at rejected
  rw [guard] at rejected
  exact p.not_completable_of_rejects _ certificate (by simpa using rejected) completed

end LeanTrominoes.CompletionPattern
