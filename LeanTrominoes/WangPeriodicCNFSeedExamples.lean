/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.WangPeriodicCNFSeedCompleteness
import LeanTrominoes.PeriodicCNFFiniteConsequencesComputability

/-! # Foreign, conflicting, and incompatible finite prescriptions -/
namespace LeanTrominoes.WangPeriodicCNF.SeedExamples
open LeanWang PeriodicCNF

private def zero : WangTile := ⟨0,0,0,0⟩
private def one : WangTile := ⟨1,1,1,1⟩
private def foreign : WangTile := ⟨2,2,2,2⟩
private def palette : TileSet := [zero,one]

example : ¬ (formula palette).Seeded (pins palette [((0,0),foreign)]) := by
  rw [seeded_iff_completable]
  rintro ⟨plane,_,retained⟩
  have fixed := retained ((0,0),foreign) (by simp)
  have member := (plane (0,0)).2
  rw [fixed] at member
  simp [palette,zero,one,foreign] at member

example : ¬ (formula palette).Seeded (pins palette [((0,0),zero),((0,0),one)]) := by
  rw [seeded_iff_completable]
  rintro ⟨plane,_,retained⟩
  have first := retained ((0,0),zero) (by simp)
  have second := retained ((0,0),one) (by simp)
  have equal := first.symm.trans second
  simp [zero,one] at equal

example : ¬ (formula palette).Seeded (pins palette [((0,0),zero),((1,0),one)]) := by
  rw [seeded_iff_completable]
  rintro ⟨plane,valid,retained⟩
  have first := retained ((0,0),zero) (by simp)
  have second := retained ((1,0),one) (by simp)
  have matched := valid.1 (0,0)
  change WangTile.HMatches (plane (0,0)).1 (plane (1,0)).1 at matched
  rw [first,second] at matched
  simp [WangTile.HMatches,zero,one] at matched

example : (formula palette).Seeded (pins palette [((0,0),zero),((20,-30),zero)]) := by
  apply seeded_of_completable
  refine ⟨fun _ => ⟨zero,by simp [palette]⟩,?_,?_⟩
  · constructor <;> intro c <;> rfl
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> rfl

private def forced : PeriodicCNF Unit := ⟨[[⟨(),(0,0),true⟩]]⟩
private def eastClause : FiniteConsequences.Clause Unit := [(((),(1,0)),true)]

example : ¬ FiniteConsequences.FiniteEntails forced eastClause 0 := by
  decide +kernel

example : FiniteConsequences.Entails forced eastClause := by
  intro a ha
  have atEast := ha (1,0) [⟨(),(0,0),true⟩] (by simp [forced])
  simpa [PeriodicClause.Holds,PeriodicLiteral.Holds,Cell.add,
    FiniteConsequences.Holds,eastClause] using atEast

end LeanTrominoes.WangPeriodicCNF.SeedExamples
