/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteIGuardedNeighborhood
import LeanTrominoes.CompletionISquareNetwork
import LeanTrominoes.FiniteSquareNetwork
import LeanTrominoes.FiniteTrominoCompletionCertificate

/-! # A finite prefill for any finite-support square-network palette -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

def squarePrefill (palette : Cell → Fin 24) (width height : Nat) : List (Placement Unit) :=
  prefill (fun c => palette (squareOfBrick c))
    (Tromino.FiniteWitness.boxList (width+height+6))

/-- The finite collar permits extraction from an arbitrary plane completion;
no periodicity is required of its tiles or Boolean signals. -/
theorem squarePrefill_correct (palette : Cell → Fin 24) (width height : Nat)
    (blank : ∀ c,¬(0≤c.1 ∧ c.1<(width:Int) ∧ 0≤c.2 ∧ c.2<(height:Int)) → palette c=0) :
    SquareHolds palette ↔ Tromino.I.Completable Set.univ
      (((squarePrefill palette width height).map fun p => p.cells (fun _ => Tromino.I.cells)).toFinset : Set (Finset Cell)) := by
  let physical := fun c => palette (squareOfBrick c)
  let locations := Tromino.FiniteWitness.boxList (width+height+6)
  have equality : prescribed physical locations=
      (((squarePrefill palette width height).map fun p => p.cells (fun _ => Tromino.I.cells)).toFinset : Set (Finset Cell)) :=
    prescribed_eq_footprints physical locations
  rw [← equality]
  constructor
  · intro model
    obtain ⟨tiles,tiling,retained⟩ := (square_holds_iff_completion palette).mp model
    exact ⟨tiles,tiling,fun _ member => retained (prescribed_subset_global physical locations member)⟩
  · rintro ⟨tiles,tiling,retained⟩
    let external := fun c => tableExternal (tableOfValue (canonicalValue physical tiles) (brickOfSquare c))
    have seams : SquareSeams external := by
      apply (square_seams_to_bricks external).mpr
      simpa only [external,brick_of_square_of_brick] using value_external_seams (canonicalValue physical tiles)
    have valid (c : Cell) (inside : LBricks.finiteSquareDomain width height c) :
        Network (palette c) (external c) := by
      have neighborhood (other : Cell) (near : BrickNear 4 (brickOfSquare c) other) : other∈locations := by
        apply List.mem_toFinset.mp
        rw [Tromino.FiniteWitness.boxList_toFinset,Tromino.FiniteWitness.mem_box]
        dsimp [BrickNear,brickOfSquare,LBricks.finiteSquareDomain] at near inside
        push_cast
        omega
      have interface := brickInterface_of_prefill physical locations tiling retained (brickOfSquare c) neighborhood
      simpa only [physical,external,square_of_brick_of_square] using canonical_network_valid tiling (brickOfSquare c) interface
    exact LBricks.squareHolds_of_finite_model width height palette blank external seams valid
end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
