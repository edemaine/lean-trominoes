/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceTerminalClassification
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceDirectionQuery
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinate

/-! # Finite terminal-coordinate queries for direct source routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- Exact unscaled terminal coordinate carried by one genuine direct-atlas
literal index. -/
def retainedDirectSourceTerminalCoordinateAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    Nat ×ₗ Nat :=
  let terminal := retainedDirectSourceLocalTerminalAt kind index
  toLex (terminal.1.angularRank, terminal.2)

/-- Total fixed-width lookup for direct terminal coordinates. Invalid
width-three indices receive an irrelevant zero fallback. -/
def retainedDirectSourceTerminalCoordinateOfQuery
    (query : RetainedDirectSourceNormalizedDirectionQuery) :
    Nat ×ₗ Nat :=
  if indexLt :
      query.literalIndex.val <
        (retainedDirectSourcePrefixChoices query.kind).length then
    retainedDirectSourceTerminalCoordinateAt query.kind
      ⟨query.literalIndex.val, indexLt⟩
  else
    toLex (0, 0)

/-- Embedding a genuine dependent atlas index in the fixed query alphabet
preserves its exact terminal coordinate. -/
@[simp] theorem retainedDirectSourceTerminalCoordinateOfQuery_index
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    retainedDirectSourceTerminalCoordinateOfQuery
        (retainedDirectSourceNormalizedDirectionQueryOfIndex kind index) =
      retainedDirectSourceTerminalCoordinateAt kind index := by
  unfold retainedDirectSourceTerminalCoordinateOfQuery
    retainedDirectSourceNormalizedDirectionQueryOfIndex
  simp only [index.isLt, dite_true]

/-- A successful final direct choice identifies the retained terminal
coordinate of its actual unscaled coordinated source route with the finite
atlas coordinate. -/
theorem retainedOccurrenceTerminalCoordinate_eq_directChoice
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    retainedOccurrenceTerminalCoordinate
        (finalCoordinatedSourceRoutes formula)
        (literal.atom, clauseIndex, literalIndex) =
      retainedDirectSourceTerminalCoordinateAt
        choice.kind choice.index := by
  have classified :=
    retainedFinalDirectSourceRouteChoice_terminalClassify
      formula clauseIndex literalIndex choice choiceLookup
  unfold retainedOccurrenceTerminalCoordinate occurrenceTerminalVector
  rw [classifiedRetainedTerminalData_eq_of_classified classified]
  unfold retainedDirectSourceTerminalCoordinateAt
  rw [retainedDirectSourceFanTerminalAt_eq_scale]
  rfl

/-- Equivalently, the fixed query already stored by the copied-clause
compiler carries that exact unscaled terminal coordinate. -/
theorem retainedOccurrenceTerminalCoordinate_eq_directChoiceQuery
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    retainedOccurrenceTerminalCoordinate
        (finalCoordinatedSourceRoutes formula)
        (literal.atom, clauseIndex, literalIndex) =
      retainedDirectSourceTerminalCoordinateOfQuery
        choice.normalizedDirectionQuery := by
  rw [retainedOccurrenceTerminalCoordinate_eq_directChoice
    formula clauseIndex literalIndex literal choice choiceLookup]
  exact
    (retainedDirectSourceTerminalCoordinateOfQuery_index
      choice.kind choice.index).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
