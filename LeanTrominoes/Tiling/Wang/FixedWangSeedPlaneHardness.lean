/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.FixedWangSeedPlaneExtension
import Lean.Util.CollectAxioms

/-! # Full-plane finite-seed hardness with one fixed Wang palette -/

noncomputable section
namespace LeanTrominoes.FixedMachineWangSeed.PlaneExtension
open LeanWang

theorem naturalClass_primrec : Primrec naturalClass :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const PointedExtension.AxisClass.origin)
    (Primrec.const PointedExtension.AxisClass.positive)

theorem seeds_primrec : Primrec seeds := by
  have layer : Primrec (fun p : Nat × WangTile =>
      PointedExtension.positionTile (naturalClass p.1) .origin) :=
    PointedExtension.positionTile_primrec.comp
      (Primrec.pair (naturalClass_primrec.comp Primrec.fst) (Primrec.const .origin))
  have pin : Primrec (fun p : Nat × WangTile =>
      (((p.1, 0) : Cell), WangTile.product
        (PointedExtension.positionTile (naturalClass p.1) .origin) p.2)) :=
    Primrec.pair (Primrec.pair
      (Computability.int_ofNat_primrec.comp Primrec.fst) (Primrec.const 0))
      (WangTile.product_primrec₂.comp layer Primrec.snd)
  exact Primrec.list_map Primrec.id (pin.comp Primrec.snd)

abbrev universalPlanePalette : TileSet := palette universalPalette

def reduction (code : Nat.Partrec.Code) : List (Cell × WangTile) :=
  seeds (universalReduction code)

theorem reduction_computable : Computable reduction :=
  seeds_primrec.to_comp.comp universalReduction_computable

theorem reduction_correct (code : Nat.Partrec.Code) :
    Completable universalPlanePalette (reduction code) ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  apply (complete_iff (corner := bottomTile
    UniversalTM0Machine.machine (UniversalTM0Machine.input (UniversalTM0Semantic.input code)) 0) ?_).trans
    (universalReduction_correct code)
  rw [universalReduction, universalSeedData_eq]
  apply List.mem_map.mpr
  refine ⟨0, ?_, rfl⟩
  simp [MachineInputTiles.tailPosition]

theorem universalPlanePalette_coREHard : CoREHard (Completable universalPlanePalette) := by
  intro A _ source hs
  obtain ⟨reduce, computable, correct⟩ := coRE_manyOneReducible_fixedNonhalting source hs
  exact ⟨reduction ∘ reduce, reduction_computable.comp computable,
    fun a => (correct a).trans (reduction_correct (reduce a)).symm⟩

open Lean Elab Command in
run_cmd do
  let name := ``universalPlanePalette_coREHard
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedMachineWangSeed.PlaneExtension
