/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-!
# Incidence graph of the periodic 3SAT-3 reduction

This file packages the connection between the logical occurrence-splitting
reduction and the periodic graph-drawing stage.  The output incidence graph
is well formed, local, and has maximum degree three.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The occurrence-split formula always has a well-formed finite periodic
incidence presentation. -/
theorem formula_incidenceGraph_isWellFormed {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (PeriodicCNF.incidenceGraph (formula source)).IsWellFormed :=
  PeriodicCNF.incidenceGraph_isWellFormed (formula source)

/-- Locality of the source formula passes through occurrence splitting and
then into its incidence graph. -/
theorem formula_incidenceGraph_isLocal {Variable : Type*}
    [DecidableEq Variable] {source : PeriodicCNF Variable}
    (sourceLocal : source.IsLocal) :
    (PeriodicCNF.incidenceGraph (formula source)).IsLocal :=
  PeriodicCNF.incidenceGraph_isLocal (formula_isLocal sourceLocal)

/-- Width three bounds clause degree, while the proved occurrence bound
bounds variable degree, so the full incidence graph has maximum degree
three. -/
theorem formula_incidenceGraph_degreeAtMostThree {Variable : Type*}
    [DecidableEq Variable] {source : PeriodicCNF Variable}
    (sourceWidth : source.WidthAtMost 3) :
    (PeriodicCNF.incidenceGraph (formula source)).DegreeAtMost 3 :=
  PeriodicCNF.incidenceGraph_degreeAtMost
    (formula_widthAtMostThree sourceWidth)
    (PeriodicCNF.occurrencesAtMost_congr_beq
      instBEqProd instBEqOfDecidableEq
      inferInstance inferInstance 3 (formula source)
      (formula_occurrencesAtMostThree source))

/-- Combined graph invariant consumed by the orthocrossing drawing
construction. -/
theorem formula_incidenceGraph_readyForDrawing {Variable : Type*}
    [DecidableEq Variable] {source : PeriodicCNF Variable}
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3) :
    (PeriodicCNF.incidenceGraph (formula source)).IsWellFormed ∧
      (PeriodicCNF.incidenceGraph (formula source)).IsLocal ∧
      (PeriodicCNF.incidenceGraph (formula source)).DegreeAtMost 3 :=
  ⟨formula_incidenceGraph_isWellFormed source,
    formula_incidenceGraph_isLocal sourceLocal,
    formula_incidenceGraph_degreeAtMostThree sourceWidth⟩

end PeriodicThreeSATThree
end LeanTrominoes
