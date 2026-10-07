/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedMachineWangSeedCompleteness
import LeanWang.Robinson.Machine.UniversalTM0.MachineData
import LeanWang.CoRE

/-! # A fixed Wang palette with co-r.e.-hard finite seed completion

The palette belongs to one universal machine. The computable reduction
changes only a finite list of bottom-row prescriptions.
-/

noncomputable section
namespace LeanTrominoes.FixedMachineWangSeed
open LeanWang MachineInputTiles

abbrev universalPalette : TileSet := fixedTiles UniversalTM0Machine.machine

def universalSeedData (source : List UniversalTM0Machine.Symbol) : List (Nat × WangTile) :=
  (List.range (UniversalTM0Machine.tailData source)).map fun p =>
    (p, toWangTile 1 (if p + 1 < UniversalTM0Machine.tailData source then 1 else 2)
      initialRowTag normalRowTag (UniversalTM0Machine.historyMachineTileData source p))

theorem universalSeedData_eq (source : List UniversalTM0Machine.Symbol) :
    universalSeedData source = bottomSeed UniversalTM0Machine.machine
      (UniversalTM0Machine.input source) := by
  apply List.map_congr_left
  intro p member
  have before : p < tailPosition (UniversalTM0Machine.input source) := List.mem_range.mp member
  simp only [bottomTile, if_pos before, UniversalTM0Machine.historyMachineTileData_eq]
  rfl

theorem universalSeedData_primrec : Primrec universalSeedData := by
  have bound : PrimrecPred (fun a : List UniversalTM0Machine.Symbol × Nat =>
      a.2 + 1 < UniversalTM0Machine.tailData a.1) :=
    Primrec.nat_lt.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
      (UniversalTM0Machine.tailData_primrec.comp Primrec.fst)
  have tile : Primrec (fun a : List UniversalTM0Machine.Symbol × Nat =>
      toWangTile 1 (if a.2 + 1 < UniversalTM0Machine.tailData a.1 then 1 else 2)
        initialRowTag normalRowTag (UniversalTM0Machine.historyMachineTileData a.1 a.2)) :=
    toWangTile_primrec.comp (Primrec.pair (Primrec.const 1)
      (Primrec.pair (Primrec.ite bound (Primrec.const 1) (Primrec.const 2))
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag) UniversalTM0Machine.historyMachineTileData_primrec))))
  exact Primrec.list_map (Primrec.list_range.comp UniversalTM0Machine.tailData_primrec)
    (Primrec.pair Primrec.snd tile).to₂

def universalReduction (code : Nat.Partrec.Code) : List (Nat × WangTile) :=
  universalSeedData (UniversalTM0Semantic.input code)

theorem universalReduction_computable : Computable universalReduction :=
  universalSeedData_primrec.to_comp.comp UniversalTM0Semantic.input_computable

theorem universalReduction_correct (code : Nat.Partrec.Code) :
    SeededQuarter universalPalette (universalReduction code) ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  rw [universalReduction, universalSeedData_eq]
  exact (seeded_iff_nonhalting (UniversalTM0Machine.input_supported
    (UniversalTM0Semantic.input code))).trans
    (not_congr ((UniversalTM0Machine.halts_iff_tm0_eval_dom
      (UniversalTM0Semantic.input code)).trans (UniversalTM0Semantic.tm0_eval_dom_iff code)))

theorem universalPalette_coREHard : CoREHard (SeededQuarter universalPalette) := by
  intro A _ source hs
  obtain ⟨reduce, computable, correct⟩ := coRE_manyOneReducible_fixedNonhalting source hs
  exact ⟨universalReduction ∘ reduce, universalReduction_computable.comp computable,
    fun a => (correct a).trans (universalReduction_correct (reduce a)).symm⟩

open Lean Elab Command in
run_cmd do
  let name := ``universalPalette_coREHard
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedMachineWangSeed
