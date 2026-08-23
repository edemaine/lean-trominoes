/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleVariableRouteSiteOrder
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms

/-! # Boundary-only routed-variable site data -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- The sites in a next-slice occurrence block not represented by the later
zero-offset occurrence-cycle suffix. -/
def nextBoundaryVariableRouteSiteBlock
    {Variable : Type*} (atom : ThreeOccurrenceVariable Variable) :
    List (VariableRouteSite (ThreeOccurrenceVariable Variable)) :=
  (variableRouteSiteBlock atom (1, 0)).filter fun site =>
    decide (site.2 ∉ neighborTranslations)

/-- All nine-site blocks contributed by the copied source-incidence prefix. -/
def occurrenceVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (VariableRouteSite (ThreeOccurrenceVariable Variable)) :=
  (occurrenceIncidences source).flatMap fun incidence =>
    variableRouteSiteBlock incidence.literal.atom incidence.edge.offset

/-- The surviving three-site block of every positive-offset copied
incidence, in source incidence order. -/
def occurrenceBoundaryVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (VariableRouteSite (ThreeOccurrenceVariable Variable)) :=
  (occurrenceIncidences source).flatMap fun incidence =>
    if incidence.edge.offset = (1, 0) then
      nextBoundaryVariableRouteSiteBlock incidence.literal.atom
    else []

/-- Whether a site from the copied-incidence prefix is absent from the later
cycle-link suffix. -/
def cycleVariableRouteSiteAbsent
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite (ThreeOccurrenceVariable Variable)) : Bool :=
  decide (site ∉ cycleLinkVariableRouteSites source)

@[simp] theorem nextBoundaryVariableRouteSiteBlock_eq
    {Variable : Type*} (atom : ThreeOccurrenceVariable Variable) :
    nextBoundaryVariableRouteSiteBlock atom =
      [(atom, (2, -1)), (atom, (2, 0)), (atom, (2, 1))] := by
  simp [nextBoundaryVariableRouteSiteBlock, variableRouteSiteBlock,
    neighborTranslations, neighborCoordinates, Cell.add]

@[simp] theorem nextBoundaryVariableRouteSiteBlock_length
    {Variable : Type*} (atom : ThreeOccurrenceVariable Variable) :
    (nextBoundaryVariableRouteSiteBlock atom).length = 3 := by
  rw [nextBoundaryVariableRouteSiteBlock_eq]
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
