/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetAssembly
import LeanTrominoes.KeyedComplementPartialTrominoRecovery

/-! # Prescribing a finite local tiling fixes its entire window state -/
namespace LeanTrominoes.Gadget

theorem window_pin_rigidity (tromino : Tromino) (original : Set Cell)
    (placements : Set (Placement Unit))
    (inside : ∀ p ∈ placements, ∀ c ∈ p.cells (fun _ => tromino.cells), c ∈ original)
    (disjoint : ∀ p ∈ placements, ∀ q ∈ placements, p ≠ q →
      Disjoint (p.cells (fun _ => tromino.cells)) (q.cells (fun _ => tromino.cells)))
    (window localRegion : Finset Cell)
    (regionInWindow : ∀ c ∈ window, c ∈ original ↔ c ∈ localRegion)
    (pattern : Finset (Placement Unit)) (valid : IsWindowTiling tromino window localRegion pattern)
    (pins : ∀ p ∈ pattern, p ∈ placements) :
    globalWindowPlacements tromino window placements = pattern := by
  classical
  apply Finset.Subset.antisymm
  · intro p member
    rcases (mem_globalWindowPlacements_iff tromino window placements p).mp member with
      ⟨selected,c,cInWindow,cCover⟩
    have cInRegion := (regionInWindow c cInWindow).mp (inside p selected c cCover)
    obtain ⟨q,⟨qMember,qCover⟩,_⟩ := valid.uniqueCover cInRegion
    by_cases equal : p = q
    · simpa [equal] using qMember
    · exact False.elim ((Finset.disjoint_left.mp (disjoint p selected q (pins q qMember) equal)) cCover qCover)
  · intro p member
    apply (mem_globalWindowPlacements_iff tromino window placements p).mpr
    exact ⟨pins p member,((mem_admissibleCandidates_iff tromino window localRegion p).mp
      (valid.1 member)).1⟩

end LeanTrominoes.Gadget

namespace LeanTrominoes.KeyedPeriodicComplement
open PlusRefinement Gadget

/-- A finite pattern of prescribed P placements fixes the local recovered
I-tromino state. The placements are retained in the original mixed tiling. -/
theorem recovered_window_pin_rigidity (original : Set Cell) (ps : Set (Placement Bool))
    {q : Polyomino} (tiling : LeanTrominoes.IsTiling (pairTiles bumpy q) Set.univ ps)
    (window localRegion : Finset Cell)
    (regionInWindow : ∀ c ∈ window, c ∈ original ↔ c ∈ localRegion)
    (pattern : Finset (Placement Unit)) (valid : IsWindowTiling .I window localRegion pattern)
    (patternInside : ∀ p ∈ pattern, ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ original)
    (pins : ∀ p ∈ pattern, (expandPlacement p).tag false ∈ ps) :
    globalWindowPlacements .I window (recoveredCoarse original ps) = pattern := by
  apply window_pin_rigidity .I original (recoveredCoarse original ps)
    (fun _ member => member.2)
    (fun _ first _ second different => recoveredCoarse_disjoint original ps tiling first second different)
    window localRegion regionInWindow pattern valid
  intro p member
  exact ⟨pins p member,patternInside p member⟩

open Lean Elab Command in
run_cmd do
  let name := ``recovered_window_pin_rigidity
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement
