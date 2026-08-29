/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Length alignment of final stable slots and terminal coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotCoordinateLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotCoordinateLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Coordinate-family cardinality is independent of the propositionally
unique decidable-equality implementation used to construct final routes. -/
theorem retainedFinalTerminalCoordinatesFrom_finalRoutes_length_irrel
    {SourceVariable ClauseVariable : Type}
    (source : PeriodicCNF SourceVariable)
    (start : Nat)
    (clauses : List (PeriodicClause ClauseVariable))
    (first second : DecidableEq SourceVariable) :
    (retainedFinalTerminalCoordinatesFrom
        (@PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          SourceVariable first source)
        start clauses).length =
      (retainedFinalTerminalCoordinatesFrom
        (@PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          SourceVariable second source)
        start clauses).length := by
  have implementationEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- Both presentations contain one item per literal in the same indexed
clause family; their values may come from different route tables. -/
theorem directSourceFinalStableRankSlotBlocksFrom_flatten_length_eq_coordinates
    (symbols : List encoding.Γ)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    (directSourceFinalStableRankSlotBlocksFrom
        decider symbols start clauses).flatten.length =
      (retainedFinalTerminalCoordinatesFrom
        routes start clauses).length := by
  unfold directSourceFinalStableRankSlotBlocksFrom
    retainedFinalTerminalCoordinatesFrom
  rw [List.length_flatten, List.length_flatMap]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro taggedClause _taggedMember
  simp [retainedOccurrenceGlobalStableTerminalSlotBlock]

end LeanTrominoes.PeriodicCNFStripReduction

end
