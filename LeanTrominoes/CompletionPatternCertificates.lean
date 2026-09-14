/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCompletion
import LeanTrominoes.TrominoFiniteExclusion

/-! # Reusable certificates for ASCII completion patterns -/

namespace LeanTrominoes.CompletionPattern

structure Pattern where
  tromino : Tromino
  region : Finset Cell
  prefill : Finset (Placement Unit)

def Pattern.target (p : Pattern) (outside : Finset Cell) : Finset Cell := p.region \ outside

def Pattern.residual (p : Pattern) (outside : Finset Cell) : Finset Cell :=
  p.target outside \ p.prefill.biUnion (Placement.cells (fun _ => p.tromino.cells))

def Pattern.Completable (p : Pattern) (outside : Finset Cell) : Prop :=
  p.tromino.Completable (p.target outside : Set Cell)
    (p.tromino.finiteFootprints p.prefill : Set (Finset Cell))

def Pattern.rejects (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteExclusion.Node) : Bool :=
  !decide (∀ q ∈ p.prefill, q.cells (fun _ => p.tromino.cells) ⊆ p.target outside) ||
    (TrominoFiniteExclusion.check p.tromino certificate &&
      decide (p.residual outside ∈ certificate.map Prod.fst))

theorem Pattern.not_completable_of_rejects (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteExclusion.Node) (rejected : p.rejects outside certificate = true) :
    ¬ p.Completable outside := by
  intro completed
  obtain ⟨legal,tiled⟩ := (p.tromino.completable_iff _ _).mp completed
  have inside : ∀ q ∈ p.prefill, q.cells (fun _ => p.tromino.cells) ⊆ p.target outside := by
    intro q hq
    exact (legal.tilesInside _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)).2
  have checked : TrominoFiniteExclusion.check p.tromino certificate = true ∧
      p.residual outside ∈ certificate.map Prod.fst := by
    have guard : decide (∀ q ∈ p.prefill,
        q.cells (fun _ => p.tromino.cells) ⊆ p.target outside) = true := by
      simpa only [decide_eq_true_eq] using inside
    unfold Pattern.rejects at rejected
    rw [guard] at rejected
    simpa using rejected
  obtain ⟨node,member,eq⟩ := List.mem_map.mp checked.2
  have noTiling := TrominoFiniteExclusion.check_sound p.tromino certificate checked.1 node member
  have cells : (p.target outside : Set Cell) \
      Tromino.occupied (p.tromino.finiteFootprints p.prefill : Set (Finset Cell)) =
      (p.residual outside : Set Cell) := by
    ext c
    simp [Pattern.residual,Tromino.occupied,Tromino.finiteFootprints]
  rw [cells,← eq] at tiled
  exact noTiling tiled

theorem Pattern.completable_of_solution (p : Pattern) (outside : Finset Cell)
    (solution : Finset (Placement Unit))
    (tiled : IsFiniteTiling (fun _ => p.tromino.cells) (p.target outside) solution)
    (retained : p.prefill ⊆ solution) : p.Completable outside :=
  p.tromino.completable_of_finiteTiling _ _ _ tiled retained

end LeanTrominoes.CompletionPattern
