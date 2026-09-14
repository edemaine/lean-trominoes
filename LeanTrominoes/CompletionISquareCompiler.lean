/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIPeriodicPattern
import LeanTrominoes.CompletionISquareNetwork
import LeanTrominoes.TrominoCompletionTranslation

/-! # Finite periodic compilation in square circuit coordinates -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.PeriodicPattern

set_option maxHeartbeats 2000000

def compileSquare (input : PeriodicPattern) (label : Cell → Fin 24) : PeriodicTrominoPrefill where
  motif := input.sites.flatMap fun site =>
    (motif (label site)).map fun p => p.shift (origin (brickOfSquare site))
  period₁ := origin (brickOfSquare (input.width,0))
  period₂ := origin (brickOfSquare (0,input.height))

theorem square_origin_repeat (input : PeriodicPattern) (label : Cell → Fin 24) (site : Cell) (i j : Int) :
    origin (brickOfSquare (input.repeatSite site i j)) =
      Cell.add (origin (brickOfSquare site))
        (Cell.add (Cell.scale i (input.compileSquare label).period₁) (Cell.scale j (input.compileSquare label).period₂)) := by
  apply Prod.ext <;> dsimp [origin,brickOfSquare,repeatSite,compileSquare,Cell.add,Cell.scale] <;> ring

theorem compileSquare_full_rank (input : PeriodicPattern) (label : Cell → Fin 24) :
    ((input.compileSquare label).occupiedRegion .I).IsFullRank := by
  unfold PeriodicRegion.IsFullRank PeriodicRegion.determinant
  dsimp [PeriodicTrominoPrefill.occupiedRegion,compileSquare,origin,brickOfSquare]
  have wp : (0 : Int) < input.width := by exact_mod_cast input.width_pos
  have hp : (0 : Int) < input.height := by exact_mod_cast input.height_pos
  have eq : (36 * (input.width : Int) + 18 * (0 - input.width)) * (162 * (input.height - 0)) -
      (162 * (0 - input.width)) * (0 + 18 * (input.height - 0)) = 5832 * input.width * input.height := by ring
  rw [eq]
  positivity

theorem compileSquare_prescribed (input : PeriodicPattern) (label : Cell → Fin 24)
    (periodic : ∀ site i j, label (input.repeatSite site i j) = label site) :
    (input.compileSquare label).prescribed .I = globalPrescribed (fun c => label (squareOfBrick c)) := by
  ext f
  constructor
  · rintro ⟨q,hq,i,j,rfl⟩
    obtain ⟨site,hs,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    refine ⟨brickOfSquare (input.repeatSite site i j),p,?_,?_⟩
    · simpa only [square_of_brick_of_square,periodic] using hp
    · rw [Placement.shift_cells_image,Placement.shift_cells_image,input.square_origin_repeat label]
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro c hc
      apply Prod.ext <;> dsimp [Function.comp_def,Cell.add] <;> omega
  · rintro ⟨location,p,hp,rfl⟩
    let site := input.residue (squareOfBrick location)
    have rep := input.repeat_residue (squareOfBrick location)
    have labels : label site = label (squareOfBrick location) := by
      rw [← rep,periodic]
    refine ⟨p.shift (origin (brickOfSquare site)),List.mem_flatMap.mpr
      ⟨site,input.residue_mem_sites _,List.mem_map.mpr ⟨p,?_,rfl⟩⟩,
      (squareOfBrick location).1 / input.width,(squareOfBrick location).2 / input.height,?_⟩
    · rwa [labels]
    · have eq := input.square_origin_repeat label site ((squareOfBrick location).1 / input.width)
        ((squareOfBrick location).2 / input.height)
      rw [rep,brick_of_square_of_brick] at eq
      rw [Placement.shift_cells_image,Placement.shift_cells_image,eq]
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro c hc
      apply Prod.ext <;> dsimp [Function.comp_def,Cell.add] <;> omega

theorem compileSquare_correct (input : PeriodicPattern) (label : Cell → Fin 24)
    (periodic : ∀ site i j, label (input.repeatSite site i j) = label site) :
    PeriodicTrominoPrefill.planeProblem .I (input.compileSquare label) ↔ SquareHolds label := by
  unfold PeriodicTrominoPrefill.planeProblem
  rw [input.compileSquare_prescribed label periodic]
  rw [← square_holds_iff_completion]
  exact and_iff_right (input.compileSquare_full_rank label)

end LeanTrominoes.CompletionPattern.IBricks.PeriodicPattern
