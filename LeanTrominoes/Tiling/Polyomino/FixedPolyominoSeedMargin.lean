/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedVertexEncoding

/-! # An effective translation puts every prescribed vertex in the forced quadrant -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed.VertexEncoding
open Gadget KeyedPeriodicComplement Computability
attribute [local irreducible] sourcePeriod coarsePeriod tilePeriod

def magnitude (pin : Pin) : Nat :=
  (location pin.1.1 pin.1.2).1.natAbs + (location pin.1.1 pin.1.2).2.natAbs

def seedMargin (seed : MatchingSeed) : Nat := seed.foldr (fun p r => magnitude p+r) 0

theorem magnitude_le_margin (seed : MatchingSeed) (pin : Pin) (member : pin ∈ seed) :
    magnitude pin ≤ seedMargin seed := by
  induction seed with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
    simp only [seedMargin,List.foldr_cons]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := ih member
      change magnitude pin ≤ magnitude first + seedMargin rest
      omega

theorem location_add (index : Nat) (base c : Cell) :
    location index (Cell.add base c) = Cell.add (location index c)
      (PeriodicCNF.Reflection.cell (Cell.scale (sourcePeriod : Int) base)) := by
  ext <;> simp only [location,Cell.add,Cell.scale,PeriodicCNF.Reflection.cell] <;> ring

theorem seed_deep (seed : MatchingSeed) (pin : Pin) (member : pin ∈ seed) :
    ShiftedGadgetReadout.Deep tilePeriod 0 (9,3)
      (location pin.1.1 (Cell.add (AugmentedSoundness.baseline (seedMargin seed)) pin.1.2)) := by
  have magnitudeBound := magnitude_le_margin seed pin member
  have xb : (location pin.1.1 pin.1.2).1.natAbs ≤ seedMargin seed := by
    unfold magnitude at magnitudeBound
    omega
  have yb : (location pin.1.1 pin.1.2).2.natAbs ≤ seedMargin seed := by
    unfold magnitude at magnitudeBound
    omega
  have xlo : -(seedMargin seed : Int) ≤ (location pin.1.1 pin.1.2).1 := by
    have := neg_abs_le (location pin.1.1 pin.1.2).1
    rw [← Int.natCast_natAbs] at this
    omega
  have yhi : (location pin.1.1 pin.1.2).2 ≤ (seedMargin seed : Int) := by
    have : (location pin.1.1 pin.1.2).2 ≤ ((location pin.1.1 pin.1.2).2.natAbs : Int) := Int.le_natAbs
    omega
  have positive : (1 : Int) ≤ sourcePeriod := by
    unfold sourcePeriod
    exact_mod_cast presentation.finalNormalizationPeriod_pos
  let k : Nat := tilePeriod+(AugmentedSoundness.windowRadius+seedMargin seed)+100
  have scaleBound : (k : Int) ≤ (sourcePeriod : Int)*(k : Int) := by
    nlinarith [mul_nonneg (show (0 : Int) ≤ sourcePeriod-1 by omega) (show (0 : Int) ≤ k by omega)]
  rw [location_add]
  change ShiftedGadgetReadout.Deep tilePeriod 0 (9,3)
    (Cell.add (location pin.1.1 pin.1.2) (PeriodicCNF.Reflection.cell (Cell.scale (sourcePeriod : Int) ((k:Int),(k:Int)))))
  dsimp [ShiftedGadgetReadout.Deep,PartialGadgetReadout.Deep,Cell.sub,Cell.add,
    PeriodicCNF.Reflection.cell,Cell.scale]
  dsimp [k] at scaleBound
  dsimp [k]
  constructor <;> omega

theorem magnitude_primrec : Primrec magnitude :=
  Primrec.nat_add.comp
    (PeriodicThreeDM.NormalizationCompiler.int_natAbs_primrec.comp
      (Primrec.fst.comp (location_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))))
    (PeriodicThreeDM.NormalizationCompiler.int_natAbs_primrec.comp
      (Primrec.snd.comp (location_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))))

theorem seedMargin_primrec : Primrec seedMargin :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (magnitude_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem baseline_primrec : Primrec (fun seed : MatchingSeed => AugmentedSoundness.baseline (seedMargin seed)) := by
  have k : Primrec (fun seed : MatchingSeed =>
      tilePeriod+(AugmentedSoundness.windowRadius+seedMargin seed)+100) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const tilePeriod)
      (Primrec.nat_add.comp (Primrec.const AugmentedSoundness.windowRadius) seedMargin_primrec)) (Primrec.const 100)
  exact Primrec.pair (int_ofNat_primrec.comp k) (int_ofNat_primrec.comp k)

end LeanTrominoes.FixedPolyominoSeed.VertexEncoding
