/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Incidence columns indexed by clause and literal ordinals -/
namespace LeanTrominoes.PositionedIncidenceRows

theorem map_indices {Variable Value : Type} (source : PositionedPeriodicCNF Variable)
    (value : Nat → Nat → Value) :
    (rows source).map (fun row => value row.1.2 row.2.2) =
      source.clauses.zipIdx.flatMap (fun clause =>
        (List.range clause.1.literals.length).map (value clause.2)) := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro clause _
  change clause.1.literals.zipIdx.map (value clause.2 ∘ Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd, List.range_eq_range']

theorem map_ordered_indices {Variable Value : Type} (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (value : Nat → Nat → Value) :
    (rows (PositionedPeriodicCNF.orderClausesByRouteDirection source routes)).map
      (fun row => value row.1.2 row.2.2) =
      source.clauses.zipIdx.flatMap (fun clause =>
        (List.range clause.1.literals.length).map (value clause.2)) := by
  rw [map_indices]
  simp only [PositionedPeriodicCNF.orderClausesByRouteDirection, List.zipIdx_map_zipIdx,
    List.flatMap_map, PositionedPeriodicCNF.orderClauseByRouteDirection_length]

theorem map_scale_indices {Variable Value : Type} (source : PositionedPeriodicCNF Variable)
    (factor : Nat) (value : Nat → Nat → Value) :
    (rows (source.scale factor)).map (fun row => value row.1.2 row.2.2) =
      (rows source).map (fun row => value row.1.2 row.2.2) := by
  rw [map_indices, map_indices]
  simp only [PositionedPeriodicCNF.scale, List.zipIdx_map, List.flatMap_map, Prod.map,
    PositionedPeriodicClause.scale]
  rfl

end LeanTrominoes.PositionedIncidenceRows
