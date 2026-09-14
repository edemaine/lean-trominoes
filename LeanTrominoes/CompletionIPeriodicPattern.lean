/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBrickLattice
import LeanTrominoes.PeriodicTrominoCompletion
import Mathlib.Tactic.Ring

/-! # Finite periodic descriptions of the I-brick palette -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

structure PeriodicPattern where
  widthPred : Nat
  heightPred : Nat
  labels : List (Fin 24)
  deriving DecidableEq, Repr

namespace PeriodicPattern

def width (input : PeriodicPattern) : Nat := input.widthPred + 1
def height (input : PeriodicPattern) : Nat := input.heightPred + 1

def residue (input : PeriodicPattern) (location : Cell) : Cell :=
  (location.1 % input.width,location.2 % input.height)

def siteLabel (input : PeriodicPattern) (location : Cell) : Fin 24 :=
  (input.labels[location.2.toNat * input.width + location.1.toNat]?).getD 0

def palette (input : PeriodicPattern) (location : Cell) : Fin 24 := input.siteLabel (input.residue location)

def sites (input : PeriodicPattern) : List Cell :=
  (List.range input.width).flatMap fun (x : Nat) => (List.range input.height).map fun (y : Nat) => ((x : Int),(y : Int))

def compile (input : PeriodicPattern) : PeriodicTrominoPrefill where
  motif := input.sites.flatMap fun location =>
    (motif (input.siteLabel location)).map fun p => p.shift (origin location)
  period₁ := origin (input.width,0)
  period₂ := origin (0,input.height)

theorem width_pos (input : PeriodicPattern) : 0 < input.width := by unfold width; omega
theorem height_pos (input : PeriodicPattern) : 0 < input.height := by unfold height; omega

theorem mem_sites (input : PeriodicPattern) (location : Cell) : location ∈ input.sites ↔
    0 ≤ location.1 ∧ location.1 < input.width ∧ 0 ≤ location.2 ∧ location.2 < input.height := by
  simp only [sites,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨x,hx,y,hy,eq⟩
    cases eq
    exact ⟨by omega,by omega,by omega,by omega⟩
  · intro bounds
    refine ⟨location.1.toNat,by omega,location.2.toNat,by omega,?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem residue_mem_sites (input : PeriodicPattern) (location : Cell) : input.residue location ∈ input.sites := by
  rw [mem_sites]
  have wp : (0 : Int) < input.width := by exact_mod_cast input.width_pos
  have hp : (0 : Int) < input.height := by exact_mod_cast input.height_pos
  dsimp [residue]
  exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ wp,
    Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hp⟩

theorem residue_of_site (input : PeriodicPattern) {location : Cell} (member : location ∈ input.sites) :
    input.residue location = location := by
  have bounds := (input.mem_sites location).mp member
  apply Prod.ext
  · exact Int.emod_eq_of_lt bounds.1 bounds.2.1
  · exact Int.emod_eq_of_lt bounds.2.2.1 bounds.2.2.2

theorem palette_of_site (input : PeriodicPattern) {location : Cell} (member : location ∈ input.sites) :
    input.palette location = input.siteLabel location := by
  unfold palette
  rw [input.residue_of_site member]

def repeatSite (input : PeriodicPattern) (site : Cell) (i j : Int) : Cell :=
  (site.1 + i * input.width,site.2 + j * input.height)

theorem residue_repeat (input : PeriodicPattern) (site : Cell) (i j : Int) :
    input.residue (input.repeatSite site i j) = input.residue site := by
  apply Prod.ext <;> simp [residue,repeatSite,Int.add_emod]

theorem palette_repeat (input : PeriodicPattern) (site : Cell) (i j : Int) :
    input.palette (input.repeatSite site i j) = input.palette site := by
  unfold palette
  rw [input.residue_repeat]

theorem repeat_residue (input : PeriodicPattern) (location : Cell) :
    input.repeatSite (input.residue location) (location.1 / input.width) (location.2 / input.height) = location := by
  apply Prod.ext <;> exact Int.emod_add_ediv_mul _ _

theorem origin_repeat (input : PeriodicPattern) (site : Cell) (i j : Int) :
    origin (input.repeatSite site i j) =
      Cell.add (origin site) (Cell.add (Cell.scale i input.compile.period₁) (Cell.scale j input.compile.period₂)) := by
  apply Prod.ext <;> dsimp [origin,repeatSite,compile,Cell.add,Cell.scale] <;> ring

theorem compile_full_rank (input : PeriodicPattern) : (input.compile.occupiedRegion .I).IsFullRank := by
  unfold PeriodicRegion.IsFullRank PeriodicRegion.determinant
  dsimp [PeriodicTrominoPrefill.occupiedRegion,compile,origin]
  simp only [add_zero,zero_mul,zero_add,sub_zero]
  have wp : (0 : Int) < input.width := by exact_mod_cast input.width_pos
  have hp : (0 : Int) < input.height := by exact_mod_cast input.height_pos
  positivity

end PeriodicPattern
end LeanTrominoes.CompletionPattern.IBricks
