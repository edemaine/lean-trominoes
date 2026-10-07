/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationCNF
import LeanTrominoes.PeriodicCNFReflection
import LeanTrominoes.KeyedComplementShiftedGadgetStates

/-! # Normalized CNF clauses recovered locally from a seeded mixed tiling -/
noncomputable section
namespace LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
open PlusRefinement Gadget

section SeededTiling
variable {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
  (holes : Polyomino) (admissible : AdmissibleHoles n holes)
  (drawing : PeriodicOrthogonalDrawing) (shift : Cell)
  (carrier : holesRegion n holes = region (original drawing shift))
  (ps : Set (Placement Bool))
  (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
  (seed : referencePlacement ∈ ps)
  (wf : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
include hn period admissible carrier tiling seed wf separated

def assignment (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool)) :
    NormalizedOrientation.AsCNF.Variable → Cell → Bool :=
  PeriodicCNF.Reflection.assignment (NormalizedOrientation.AsCNF.assignment drawing (readout drawing shift ps))

theorem clause_sound (translate : Cell)
    (safe : ∀ location ∈ NormalizedOrientation.AsCNF.positions drawing,
      Deep n 3 shift (NormalizedOrientation.AsCNF.lift drawing location translate)) :
    ∀ clause ∈ (NormalizedOrientation.AsCNF.formula drawing).clauses,
      clause.Holds (NormalizedOrientation.AsCNF.assignment drawing (readout drawing shift ps)) translate := by
  intro clause member
  obtain ⟨location,listed,localMember⟩ := List.mem_flatMap.mp member
  apply (NormalizedOrientation.AsCNF.clausesAt_correct drawing _ location translate).2 _ clause localMember
  rw [NormalizedOrientation.AsCNF.orientation_assignment]
  constructor
  · exact vertex_sound hn period holes admissible drawing shift carrier ps tiling seed wf separated
      (deep_mono (by decide : 2 ≤ 3) (safe location listed))
  · intro side active
    cases colorMatch : (drawing.getAt (NormalizedOrientation.AsCNF.lift drawing location translate)).portColor side with
    | none => simp [colorMatch] at active
    | some color =>
      exact edge_opposite hn period holes admissible drawing shift carrier ps tiling seed wf separated
        (safe location listed) side color colorMatch

theorem reflected_clause_sound (translate : Cell)
    (safe : ∀ location ∈ NormalizedOrientation.AsCNF.positions drawing,
      Deep n 3 shift (NormalizedOrientation.AsCNF.lift drawing location (PeriodicCNF.Reflection.cell translate))) :
    ∀ clause ∈ (PeriodicCNF.Reflection.formula (NormalizedOrientation.AsCNF.formula drawing)).clauses,
      clause.Holds (assignment drawing shift ps) translate := by
  intro clause member
  obtain ⟨originalClause,originalMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨literal,literalMember,holds⟩ := clause_sound hn period holes admissible drawing shift carrier ps tiling seed
    wf separated (PeriodicCNF.Reflection.cell translate) safe originalClause originalMember
  refine ⟨PeriodicCNF.Reflection.literal literal,List.mem_map.mpr ⟨literal,literalMember,rfl⟩,?_⟩
  apply (PeriodicCNF.Reflection.literal_holds _ translate literal).2
  simpa only [assignment,PeriodicCNF.Reflection.assignment_assignment] using holds

end SeededTiling
end LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
