/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementPartialTrominoRecovery
import LeanTrominoes.GadgetAssembly

/-! # Exact gadget-window tilings recovered without moving the seed -/
namespace LeanTrominoes.KeyedPeriodicComplement
open PlusRefinement Gadget

def recoveredRegion (original : Set Cell) (ps : Set (Placement Bool)) : Set Cell :=
  {c | ∃ p ∈ recoveredCoarse original ps, c ∈ p.cells (fun _ => Tromino.I.cells)}

theorem recoveredCoarse_tiling (original : Set Cell) (ps : Set (Placement Bool))
    {q : Polyomino} (tiling : LeanTrominoes.IsTiling (pairTiles bumpy q) Set.univ ps) :
    LeanTrominoes.IsTiling (fun _ : Unit => Tromino.I.cells)
      (recoveredRegion original ps) (recoveredCoarse original ps) := by
  constructor
  · intro p member c cover
    exact ⟨p,member,cover⟩
  · rintro c ⟨p,member,cover⟩
    refine ⟨p,⟨member,cover⟩,?_⟩
    rintro other ⟨otherMember,otherCover⟩
    by_contra different
    exact (Finset.disjoint_left.mp
      (recoveredCoarse_disjoint original ps tiling otherMember member different)) otherCover cover

/-- Every deep finite window has the exact local tiling required by the
verified I-gadget tables, extracted from the original mixed tiling. -/
theorem recoveredCoarse_windowTiling {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = region original)
    (ps : Set (Placement Bool))
    (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps)
    (window localRegion : Finset Cell) (localInside : localRegion ⊆ window)
    (regionInWindow : ∀ c ∈ window, c ∈ original ↔ c ∈ localRegion)
    (deep : ∀ c ∈ window, (n : Int)+4 ≤ c.1 ∧ c.2 ≤ -(n : Int)-4) :
    IsWindowTiling .I window localRegion
      (globalWindowPlacements .I window (recoveredCoarse original ps)) := by
  apply Gadget.IsTiling.isWindowTiling (recoveredCoarse_tiling original ps tiling)
    window localRegion localInside
  intro c cMember
  rw [← regionInWindow c cMember]
  constructor
  · rintro ⟨p,member,cover⟩
    exact member.2 c cover
  · intro inside
    have bounds := deep c cMember
    obtain ⟨p,⟨member,cover⟩,_⟩ := recoveredCoarse_uniqueCover hn period holes admissible
      original carrier ps tiling seed inside bounds.1 bounds.2
    exact ⟨p,member,cover⟩

open Lean Elab Command in
run_cmd do
  let name := ``recoveredCoarse_windowTiling
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement
