/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.WangPeriodicCNF
import LeanTrominoes.PeriodicCNFSeededFiniteSearch
import LeanTrominoes.FixedWangSeedPlaneExtension

/-! # Prescribed Wang tiles as finite Boolean prescriptions

At each prescribed cell, all palette bits are fixed to the indicator of the
prescribed tile. A positive bit for the prescribed tile is included as well.
This rejects foreign tiles and conflicting prescriptions without assumptions
on the input seed.
-/
namespace LeanTrominoes.WangPeriodicCNF
open LeanWang

abbrev WangSeed := List (Cell × WangTile)

def pins (tiles : TileSet) (seed : WangSeed) : PeriodicCNF.Seed WangTile :=
  seed.flatMap fun p => ((p.2,p.1),true) ::
    tiles.map (fun tile => ((tile,p.1),decide (tile = p.2)))

theorem pins_positive {tiles : TileSet} {seed : WangSeed} {p : Cell × WangTile}
    (member : p ∈ seed) : ((p.2,p.1),true) ∈ pins tiles seed :=
  List.mem_flatMap.mpr ⟨p,member,by simp⟩

theorem pins_indicator {tiles : TileSet} {seed : WangSeed} {p : Cell × WangTile}
    (member : p ∈ seed) {tile : WangTile} (tileMember : tile ∈ tiles) :
    ((tile,p.1),decide (tile = p.2)) ∈ pins tiles seed :=
  List.mem_flatMap.mpr ⟨p,member,List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨tile,tileMember,rfl⟩)⟩

def indicator {tiles : TileSet} (tiling : Cell → TileIn tiles) :
    WangTile → Cell → Bool := fun tile cell => decide ((tiling cell).1 = tile)

theorem indicator_satisfies {tiles : TileSet} (tiling : Cell → TileIn tiles)
    (valid : ValidPlaneTiling tiles tiling) : (formula tiles).Satisfies (indicator tiling) := by
  let assignment : WangTile → Cell → Bool :=
    fun tile cell => decide ((tiling cell).1 = tile)
  change (formula tiles).Satisfies assignment
  intro translate clause clause_mem
  simp only [formula, List.mem_cons, List.mem_append] at clause_mem
  rcases clause_mem with (rfl | clause_mem) | clause_mem
  · refine ⟨positive (tiling translate).1 here, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(tiling translate).1, (tiling translate).2, rfl⟩
    · simp [PeriodicLiteral.Holds, assignment, positive, here, Cell.add]
  · simp only [horizontalClauses, List.mem_filterMap] at clause_mem
    rcases clause_mem with ⟨⟨left, right⟩, pair_mem, clause_eq⟩
    simp only at clause_eq
    split at clause_eq
    · contradiction
    · simp only [Option.some.injEq] at clause_eq
      subst clause
      rw [mem_orderedPairs] at pair_mem
      by_cases left_here : (tiling translate).1 = left
      · refine ⟨negative right east, by simp, ?_⟩
        simp only [PeriodicLiteral.Holds, negative, assignment, east, Cell.add,
          decide_eq_false_iff_not]
        intro right_east
        apply ‹¬ WangTile.HMatches left right›
        rw [← left_here, ← right_east]
        simpa using valid.1 translate
      · refine ⟨negative left here, by simp, ?_⟩
        simpa [PeriodicLiteral.Holds, negative, assignment, here, Cell.add]
  · simp only [verticalClauses, List.mem_filterMap] at clause_mem
    rcases clause_mem with ⟨⟨lower, upper⟩, pair_mem, clause_eq⟩
    simp only at clause_eq
    split at clause_eq
    · contradiction
    · simp only [Option.some.injEq] at clause_eq
      subst clause
      rw [mem_orderedPairs] at pair_mem
      by_cases lower_here : (tiling translate).1 = lower
      · refine ⟨negative upper north, by simp, ?_⟩
        simp only [PeriodicLiteral.Holds, negative, assignment, north, Cell.add,
          decide_eq_false_iff_not]
        intro upper_north
        apply ‹¬ WangTile.VMatches lower upper›
        rw [← lower_here, ← upper_north]
        simpa using valid.2 translate
      · refine ⟨negative lower here, by simp, ?_⟩
        simpa [PeriodicLiteral.Holds, negative, assignment, here, Cell.add]

theorem seeded_of_completable {tiles : TileSet} {seed : WangSeed}
    (completed : FixedMachineWangSeed.PlaneExtension.Completable tiles seed) :
    (formula tiles).Seeded (pins tiles seed) := by
  obtain ⟨tiling,valid,retained⟩ := completed
  refine ⟨indicator tiling,indicator_satisfies tiling valid,?_⟩
  intro pin member
  obtain ⟨p,pMember,pinMember⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.mem_map] at pinMember
  rcases pinMember with rfl | ⟨tile,_,rfl⟩
  · simp [indicator,retained p pMember]
  · simp only [indicator,retained p pMember]
    simp only [eq_comm]

theorem completable_of_seeded {tiles : TileSet} {seed : WangSeed}
    (completed : (formula tiles).Seeded (pins tiles seed)) :
    FixedMachineWangSeed.PlaneExtension.Completable tiles seed := by
  obtain ⟨assignment,satisfies,retained⟩ := completed
  have active_exists :
      ∀ cell : Cell, ∃ tile : WangTile, tile ∈ tiles ∧ assignment tile cell = true := by
    intro cell
    rcases satisfies cell (atLeastOneClause tiles) (atLeastOneClause_mem tiles) with
      ⟨literal, literal_mem, literal_holds⟩
    simp only [atLeastOneClause, List.mem_map] at literal_mem
    rcases literal_mem with ⟨tile, tile_mem, rfl⟩
    exact ⟨tile, tile_mem, by
      simpa [PeriodicLiteral.Holds, positive, here, Cell.add] using literal_holds⟩
  choose chosen chosen_mem chosen_active using active_exists
  let tiling : Cell → TileIn tiles := fun cell => ⟨chosen cell, chosen_mem cell⟩
  refine ⟨tiling, ⟨?_, ?_⟩, ?_⟩
  · intro cell
    by_contra incompatible
    have clause_holds := satisfies cell
      [negative (chosen cell) here, negative (chosen (cell.1 + 1, cell.2)) east]
      (horizontalClause_mem (chosen_mem cell) (chosen_mem (cell.1 + 1, cell.2))
        incompatible)
    rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
    rcases literal_mem with rfl | rfl
    · simp [PeriodicLiteral.Holds, negative, here, Cell.add,
        chosen_active cell] at literal_holds
    · simp [PeriodicLiteral.Holds, negative, east, Cell.add,
        chosen_active (cell.1 + 1, cell.2)] at literal_holds
  · intro cell
    by_contra incompatible
    have clause_holds := satisfies cell
      [negative (chosen cell) here, negative (chosen (cell.1, cell.2 + 1)) north]
      (verticalClause_mem (chosen_mem cell) (chosen_mem (cell.1, cell.2 + 1))
        incompatible)
    rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
    rcases literal_mem with rfl | rfl
    · simp [PeriodicLiteral.Holds, negative, here, Cell.add,
        chosen_active cell] at literal_holds
    · simp [PeriodicLiteral.Holds, negative, north, Cell.add,
        chosen_active (cell.1, cell.2 + 1)] at literal_holds
  · intro p member
    have fixed := retained _ (pins_indicator member (chosen_mem p.1))
    have active := chosen_active p.1
    change chosen p.1 = p.2
    have : decide (chosen p.1 = p.2) = true := by
      simpa only [active] using fixed.symm
    exact of_decide_eq_true this

theorem seeded_iff_completable (tiles : TileSet) (seed : WangSeed) :
    (formula tiles).Seeded (pins tiles seed) ↔
      FixedMachineWangSeed.PlaneExtension.Completable tiles seed :=
  ⟨completable_of_seeded,seeded_of_completable⟩

end LeanTrominoes.WangPeriodicCNF
