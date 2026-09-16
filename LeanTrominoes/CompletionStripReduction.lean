/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripValidity
import LeanTrominoes.PeriodicStripComplement
import LeanTrominoes.StripFrontierReconstruction

/-! # Strip completion as tiling an explicit uncovered periodic subset -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill

/-- The occupied strip cells. Out-of-strip preplacements are checked separately. -/
def occupiedStrip (t : Tromino) (input : PeriodicStripTrominoPrefill) : PeriodicStrip :=
  ⟨input.height,input.period,input.motif.flatMap (PeriodicTrominoPrefill.placementCells t)⟩

theorem occupiedStrip_carrier (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (occupiedStrip t input).carrier = input.region ∩ (input.periodic.occupiedRegion t).carrier := by
  ext c
  constructor
  · rintro ⟨hy,hw,b,hb,i,eq⟩
    refine ⟨⟨hy,hw⟩,b,hb,i,0,?_⟩
    simpa [occupiedStrip,periodic,PeriodicTrominoPrefill.occupiedRegion,Cell.add,Cell.scale] using eq
  · rintro ⟨⟨hy,hw⟩,b,hb,i,j,eq⟩
    refine ⟨hy,hw,b,hb,i,?_⟩
    simpa [occupiedStrip,periodic,PeriodicTrominoPrefill.occupiedRegion,Cell.add,Cell.scale] using eq

def uncoveredStrip (t : Tromino) (input : PeriodicStripTrominoPrefill) : PeriodicStrip :=
  (occupiedStrip t input).complement

theorem uncoveredStrip_carrier (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hp : 0 < input.period) :
    (uncoveredStrip t input).carrier = input.region \ (input.periodic.occupiedRegion t).carrier := by
  rw [uncoveredStrip,PeriodicStrip.complement_carrier _ hp,occupiedStrip_carrier]
  ext c
  change (c ∈ input.region ∧ ¬ (c ∈ input.region ∧ c ∈ (input.periodic.occupiedRegion t).carrier)) ↔ _
  simp only [Set.mem_sdiff]
  tauto

theorem uncoveredStrip_wellFormed (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (hp : 0 < input.period) :
    (uncoveredStrip t input).IsWellFormed :=
  PeriodicStrip.complement_wellFormed _ hh hp

theorem problem_iff_uncovered (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    problem t input ↔ 0 < input.height ∧ 0 < input.period ∧ Valid t input ∧
      PeriodicStripTrominoTiling t (uncoveredStrip t input) := by
  rw [problem_iff,← valid_iff_partial]
  apply and_congr_right
  intro hh
  apply and_congr_right
  intro hp
  rw [PeriodicStripTrominoTiling,and_iff_right (uncoveredStrip_wellFormed t input hh hp),
    uncoveredStrip_carrier t input hp]

/-- An executable decider; polynomial-space certification is supplied separately. -/
instance problemDecidable (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    Decidable (problem t input) :=
  decidable_of_iff _ (problem_iff_uncovered t input).symm

theorem uncoveredStrip_motif_length (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (uncoveredStrip t input).motif.length ≤ input.period * input.height :=
  PeriodicStrip.complement_motif_length _

end LeanTrominoes.PeriodicStripTrominoPrefill
