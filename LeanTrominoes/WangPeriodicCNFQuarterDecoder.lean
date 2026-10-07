/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.WangPeriodicCNFSeed

/-! # Decoding seeded Wang tilings from clauses valid only in the positive quadrant -/
namespace LeanTrominoes.WangPeriodicCNF
open LeanWang FixedMachineWangSeed

def QuarterSatisfies (tiles : TileSet) (a : WangTile → Cell → Bool) : Prop :=
  ∀ p : Nat × Nat, ∀ clause ∈ (formula tiles).clauses, clause.Holds a (p.1,p.2)

def bottomSeed (seed : List (Nat × WangTile)) : WangSeed := seed.map fun p => ((p.1,0),p.2)

theorem seededQuarter_of_satisfies (tiles : TileSet) (seed : List (Nat × WangTile))
    (a : WangTile → Cell → Bool) (satisfies : QuarterSatisfies tiles a)
    (retained : ∀ pin ∈ pins tiles (bottomSeed seed), a pin.1.1 pin.1.2 = pin.2) :
    SeededQuarter tiles seed := by
  classical
  have active_exists (p : Nat × Nat) : ∃ tile ∈ tiles, a tile (p.1,p.2) = true := by
    obtain ⟨literal,member,holds⟩ := satisfies p (atLeastOneClause tiles) (atLeastOneClause_mem tiles)
    obtain ⟨tile,tileMember,rfl⟩ := List.mem_map.mp member
    exact ⟨tile,tileMember,by simpa [PeriodicLiteral.Holds,positive,here,Cell.add] using holds⟩
  choose chosen chosen_mem chosen_active using active_exists
  let quarter : Nat × Nat → TileIn tiles := fun p => ⟨chosen p,chosen_mem p⟩
  refine ⟨quarter,⟨?_,?_⟩,?_⟩
  · intro p
    change (chosen p).HMatches (chosen (p.1+1,p.2))
    by_contra incompatible
    obtain ⟨literal,member,holds⟩ := satisfies p _
      (horizontalClause_mem (chosen_mem p) (chosen_mem (p.1+1,p.2)) incompatible)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · simp [PeriodicLiteral.Holds,negative,here,Cell.add,chosen_active p] at holds
    · have active : a (chosen (p.1+1,p.2)) ((p.1:Int)+1,p.2) = true := by
        simpa using chosen_active (p.1+1,p.2)
      simp [PeriodicLiteral.Holds,negative,east,Cell.add,active] at holds
  · intro p
    change (chosen p).VMatches (chosen (p.1,p.2+1))
    by_contra incompatible
    obtain ⟨literal,member,holds⟩ := satisfies p _
      (verticalClause_mem (chosen_mem p) (chosen_mem (p.1,p.2+1)) incompatible)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · simp [PeriodicLiteral.Holds,negative,here,Cell.add,chosen_active p] at holds
    · have active : a (chosen (p.1,p.2+1)) (p.1,(p.2:Int)+1) = true := by
        simpa using chosen_active (p.1,p.2+1)
      simp [PeriodicLiteral.Holds,negative,north,Cell.add,active] at holds
  · rintro ⟨position,tile⟩ member
    have pinMember : (((position:Int),0),tile) ∈ bottomSeed seed :=
      List.mem_map.mpr ⟨(position,tile),member,rfl⟩
    have fixed := retained _ (pins_indicator pinMember (chosen_mem (position,0)))
    have active := chosen_active (position,0)
    have active' : a (chosen (position,0)) ((position:Int),0) = true := by simpa using active
    change chosen (position,0) = tile
    have fixed' : decide (chosen (position,0) = tile) = true := by
      simpa only [active'] using fixed.symm
    exact of_decide_eq_true fixed'

end LeanTrominoes.WangPeriodicCNF
