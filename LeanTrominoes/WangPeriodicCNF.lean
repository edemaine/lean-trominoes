import LeanTrominoes.PeriodicCNF
import LeanWang.Basic

/-!
# Wang tilings as periodic CNF

This file gives the first semantic leg of the hardness reduction.  A Wang
tileset is translated to a finite collection of Boolean clauses repeated at
every cell of the plane.  An atom says that a particular Wang tile is active at
a particular cell.  Each cell has at least one active tile, and incompatible
tiles may not both be active across a shared edge.

Uniqueness is deliberately unnecessary: choosing any active tile at each cell
produces a Wang tiling because every incompatible neighboring pair is forbidden.
-/

namespace LeanTrominoes
namespace WangPeriodicCNF

open LeanWang

/-- The zero, east, and north offsets used by the local Wang constraints. -/
def here : Cell := (0, 0)
def east : Cell := (1, 0)
def north : Cell := (0, 1)

/-- A positive Wang-tile atom at a local offset. -/
def positive (tile : WangTile) (offset : Cell) : PeriodicLiteral WangTile :=
  ⟨tile, offset, true⟩

/-- A negative Wang-tile atom at a local offset. -/
def negative (tile : WangTile) (offset : Cell) : PeriodicLiteral WangTile :=
  ⟨tile, offset, false⟩

/-- All ordered pairs drawn from a finite tileset. -/
def orderedPairs (tiles : TileSet) : List (WangTile × WangTile) :=
  tiles.flatMap fun first => tiles.map fun second => (first, second)

theorem mem_orderedPairs {tiles : TileSet} {first second : WangTile} :
    (first, second) ∈ orderedPairs tiles ↔ first ∈ tiles ∧ second ∈ tiles := by
  simp [orderedPairs]

/-- The clause asserting that some tile from the tileset is active here. -/
def atLeastOneClause (tiles : TileSet) : PeriodicClause WangTile :=
  tiles.map fun tile => positive tile here

/-- Binary clauses excluding horizontally incompatible active tiles. -/
def horizontalClauses (tiles : TileSet) : List (PeriodicClause WangTile) :=
  (orderedPairs tiles).filterMap fun pair =>
    if WangTile.HMatches pair.1 pair.2 then
      none
    else
      some [negative pair.1 here, negative pair.2 east]

/-- Binary clauses excluding vertically incompatible active tiles. -/
def verticalClauses (tiles : TileSet) : List (PeriodicClause WangTile) :=
  (orderedPairs tiles).filterMap fun pair =>
    if WangTile.VMatches pair.1 pair.2 then
      none
    else
      some [negative pair.1 here, negative pair.2 north]

/-- The periodic CNF encoding of a Wang tileset. -/
def formula (tiles : TileSet) : PeriodicCNF WangTile where
  clauses := atLeastOneClause tiles :: horizontalClauses tiles ++ verticalClauses tiles

theorem atLeastOneClause_mem (tiles : TileSet) :
    atLeastOneClause tiles ∈ (formula tiles).clauses := by
  simp [formula]

theorem horizontalClause_mem {tiles : TileSet} {left right : WangTile}
    (left_mem : left ∈ tiles) (right_mem : right ∈ tiles)
    (incompatible : ¬ WangTile.HMatches left right) :
    [negative left here, negative right east] ∈ (formula tiles).clauses := by
  have horizontal_mem :
      [negative left here, negative right east] ∈ horizontalClauses tiles := by
    rw [horizontalClauses, List.mem_filterMap]
    refine ⟨(left, right), mem_orderedPairs.2 ⟨left_mem, right_mem⟩, ?_⟩
    simp [incompatible]
  simp only [formula, List.mem_append, List.mem_cons]
  left
  exact Or.inr horizontal_mem

theorem verticalClause_mem {tiles : TileSet} {lower upper : WangTile}
    (lower_mem : lower ∈ tiles) (upper_mem : upper ∈ tiles)
    (incompatible : ¬ WangTile.VMatches lower upper) :
    [negative lower here, negative upper north] ∈ (formula tiles).clauses := by
  have vertical_mem :
      [negative lower here, negative upper north] ∈ verticalClauses tiles := by
    rw [verticalClauses, List.mem_filterMap]
    refine ⟨(lower, upper), mem_orderedPairs.2 ⟨lower_mem, upper_mem⟩, ?_⟩
    simp [incompatible]
  simp only [formula, List.mem_append, List.mem_cons]
  exact Or.inr vertical_mem

theorem atLeastOneClause_isLocal (tiles : TileSet) :
    (atLeastOneClause tiles).IsLocal := by
  intro first first_mem second second_mem
  simp only [atLeastOneClause, List.mem_map] at first_mem second_mem
  rcases first_mem with ⟨firstTile, _, rfl⟩
  rcases second_mem with ⟨secondTile, _, rfl⟩
  simp [PeriodicClause.offsetDistance, positive, here]

theorem horizontalClauses_areLocal {tiles : TileSet}
    {clause : PeriodicClause WangTile} (clause_mem : clause ∈ horizontalClauses tiles) :
    clause.IsLocal := by
  simp only [horizontalClauses, List.mem_filterMap] at clause_mem
  rcases clause_mem with ⟨⟨left, right⟩, _, clause_eq⟩
  split at clause_eq
  · contradiction
  · simp only [Option.some.injEq] at clause_eq
    subst clause
    intro first first_mem second second_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at first_mem second_mem
    rcases first_mem with rfl | rfl <;>
      rcases second_mem with rfl | rfl <;>
      simp [PeriodicClause.offsetDistance, negative, here, east]

theorem verticalClauses_areLocal {tiles : TileSet}
    {clause : PeriodicClause WangTile} (clause_mem : clause ∈ verticalClauses tiles) :
    clause.IsLocal := by
  simp only [verticalClauses, List.mem_filterMap] at clause_mem
  rcases clause_mem with ⟨⟨lower, upper⟩, _, clause_eq⟩
  split at clause_eq
  · contradiction
  · simp only [Option.some.injEq] at clause_eq
    subst clause
    intro first first_mem second second_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at first_mem second_mem
    rcases first_mem with rfl | rfl <;>
      rcases second_mem with rfl | rfl <;>
      simp [PeriodicClause.offsetDistance, negative, here, north]

/-- The Wang encoding is local: every protoclauses is contained in one cell or
crosses exactly one horizontal or vertical grid edge. -/
theorem formula_isLocal (tiles : TileSet) :
    (formula tiles).IsLocal := by
  intro clause clause_mem
  simp only [formula, List.mem_append, List.mem_cons] at clause_mem
  rcases clause_mem with (rfl | clause_mem) | clause_mem
  · exact atLeastOneClause_isLocal tiles
  · exact horizontalClauses_areLocal clause_mem
  · exact verticalClauses_areLocal clause_mem

/-- Every Wang tiling gives a satisfying periodic Boolean assignment. -/
theorem satisfiable_of_tilesPlane {tiles : TileSet} :
    TilesPlane tiles → (formula tiles).Satisfiable := by
  rintro ⟨tiling, valid⟩
  let assignment : WangTile → Cell → Bool :=
    fun tile cell => decide ((tiling cell).1 = tile)
  refine ⟨assignment, ?_⟩
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

/-- Every satisfying periodic assignment yields a Wang tiling by choosing one
active tile at each cell. -/
theorem tilesPlane_of_satisfiable {tiles : TileSet} :
    (formula tiles).Satisfiable → TilesPlane tiles := by
  rintro ⟨assignment, satisfies⟩
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
  refine ⟨tiling, ?_, ?_⟩
  · intro cell
    by_contra incompatible
    have clause_holds := satisfies cell
      [negative (chosen cell) here, negative (chosen (cell.1 + 1, cell.2)) east]
      (horizontalClause_mem (chosen_mem cell) (chosen_mem (cell.1 + 1, cell.2))
        incompatible)
    rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
    rcases literal_mem with rfl | rfl
    · simpa [PeriodicLiteral.Holds, negative, here, Cell.add,
        chosen_active cell] using literal_holds
    · simpa [PeriodicLiteral.Holds, negative, east, Cell.add,
        chosen_active (cell.1 + 1, cell.2)] using literal_holds
  · intro cell
    by_contra incompatible
    have clause_holds := satisfies cell
      [negative (chosen cell) here, negative (chosen (cell.1, cell.2 + 1)) north]
      (verticalClause_mem (chosen_mem cell) (chosen_mem (cell.1, cell.2 + 1))
        incompatible)
    rcases clause_holds with ⟨literal, literal_mem, literal_holds⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
    rcases literal_mem with rfl | rfl
    · simpa [PeriodicLiteral.Holds, negative, here, Cell.add,
        chosen_active cell] using literal_holds
    · simpa [PeriodicLiteral.Holds, negative, north, Cell.add,
        chosen_active (cell.1, cell.2 + 1)] using literal_holds

/-- The Wang tileset tiles the plane exactly when its periodic CNF is
satisfiable. -/
theorem formula_correct (tiles : TileSet) :
    TilesPlane tiles ↔ (formula tiles).Satisfiable :=
  ⟨satisfiable_of_tilesPlane, tilesPlane_of_satisfiable⟩

end WangPeriodicCNF
end LeanTrominoes
