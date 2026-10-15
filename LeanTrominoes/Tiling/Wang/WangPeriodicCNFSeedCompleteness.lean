/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.WangPeriodicCNFSeed
import LeanTrominoes.Tiling.Wang.WangPeriodicCNFComputability
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededCoRE
import LeanTrominoes.Tiling.Wang.FixedWangSeedPlaneHardness

/-! # One fixed local CNF formula with co-r.e.-complete finite prescriptions -/
noncomputable section
namespace LeanTrominoes.WangPeriodicCNF
open LeanWang

theorem pins_primrec : Primrec₂ pins := by
  have bits : Primrec (fun a : TileSet × (Cell × WangTile) =>
      a.1.map (fun tile => ((tile,a.2.1),decide (tile = a.2.2)))) :=
    Primrec.list_map Primrec.fst
      (Primrec.pair
        (Primrec.pair Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        ((Primrec.eq.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).decide))
  have one : Primrec (fun a : TileSet × (Cell × WangTile) =>
      ((a.2.2,a.2.1),true) ::
        a.1.map (fun tile => ((tile,a.2.1),decide (tile = a.2.2)))) :=
    Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
        (Primrec.const true)) bits
  exact Primrec.list_flatMap Primrec.snd
    (one.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))

abbrev fixedFormula : PeriodicCNF WangTile :=
  formula FixedMachineWangSeed.PlaneExtension.universalPlanePalette

def fixedSeedReduction (seed : WangSeed) : PeriodicCNF.Seed WangTile :=
  pins FixedMachineWangSeed.PlaneExtension.universalPlanePalette seed

theorem fixedSeedReduction_primrec : Primrec fixedSeedReduction :=
  pins_primrec.comp (Primrec.const _) Primrec.id

theorem fixedFormula_seeded_coREHard : CoREHard fixedFormula.Seeded := by
  intro A _ source hs
  obtain ⟨reduce,computable,correct⟩ :=
    FixedMachineWangSeed.PlaneExtension.universalPlanePalette_coREHard source hs
  refine ⟨fixedSeedReduction ∘ reduce,fixedSeedReduction_primrec.to_comp.comp computable,?_⟩
  intro a
  exact (correct a).trans (seeded_iff_completable _ _).symm

theorem fixedFormula_seeded_coREComplete : CoREComplete fixedFormula.Seeded :=
  ⟨PeriodicCNF.fixed_seeded_coRE fixedFormula,fixedFormula_seeded_coREHard⟩

open Lean Elab Command in
run_cmd do
  let name := ``fixedFormula_seeded_coREComplete
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.WangPeriodicCNF
