import LeanTrominoes.CompletionIRegionGeometry

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

theorem straight_span (p : Placement Unit) {c d : Cell}
    (hc : c ∈ p.cells (fun _ => Tromino.I.cells))
    (hd : d ∈ p.cells (fun _ => Tromino.I.cells)) :
    c.1 - 2 ≤ d.1 ∧ d.1 ≤ c.1 + 2 ∧ c.2 - 2 ≤ d.2 ∧ d.2 ≤ c.2 + 2 := by
  have checked : ∀ s : SquareSymmetry, ∀ u ∈ Tromino.I.cells, ∀ v ∈ Tromino.I.cells,
      (s.act u).1 - 2 ≤ (s.act v).1 ∧ (s.act v).1 ≤ (s.act u).1 + 2 ∧
      (s.act u).2 - 2 ≤ (s.act v).2 ∧ (s.act v).2 ≤ (s.act u).2 + 2 := by decide +kernel
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
  have bounds := checked p.symmetry u hu v hv
  dsimp [Cell.add]
  omega

def Atom.Interior (a : Atom) (c : Cell) : Prop :=
  2 ≤ c.1 ∧ c.1 + 2 < a.width ∧ 3 ≤ c.2 ∧ c.2 + 2 < a.height

instance (a : Atom) (c : Cell) : Decidable (a.Interior c) := by
  unfold Atom.Interior
  infer_instance

theorem Atom.interior_contained (a : Atom) {c : Cell} (interior : a.Interior c)
    (p : Placement Unit) (covers : c ∈ p.cells (fun _ => Tromino.I.cells)) :
    p.cells (fun _ => Tromino.I.cells) ⊆ a.pattern.region := by
  intro d hd
  have bounds := straight_span p covers hd
  apply (a.mem_region d).mpr
  unfold CompletionGuardedShape.Member
  dsimp [Atom.Interior] at interior
  exact ⟨by omega,by omega,Or.inl ⟨by omega,by omega⟩⟩

theorem Atom.guarded_of_fringe (a : Atom) (fringe : Finset Cell)
    (covered : ∀ c ∈ a.core, a.Interior c ∨ c ∈ fringe)
    (checked : CompletionBarrier.GuardedCheck .I fringe a.pattern.region
      a.fixed a.available) :
    CompletionBarrier.GuardedCheck .I a.core a.pattern.region
      a.fixed a.available := by
  intro c hc p hp
  rcases covered c hc with interior | boundary
  · exact Or.inl (a.interior_contained interior p
      ((TrominoAssignment.mem_coveringPlacements_iff .I c p).mp
        ((TrominoAssignment.mem_coveringPlacementList_iff .I c p).mp hp)))
  · exact checked c boundary p hp

end LeanTrominoes.CompletionPattern.IBricks
