/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMDegree

/-!
# Canonical matching for the assembled planar 3DM reduction

A plane-wide exact-one assignment determines a local alternating state in
every variable-occurrence module.  Its common RGB connector signal is the
truth value of the signed source literal.  At each clause translate, the
three terminal signals select one of the explicit `EFI`, `BDH`, or `ACG`
covers of the nine-triple clause core.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Look up the source literal at one clause/literal position. -/
def literalAt {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    Option (PeriodicLiteral Variable) :=
  source.clauses[clauseIndex]?.bind fun clause =>
    clause[literalIndex]?

/-- Boolean carried by one signed variable connector. -/
def occurrenceSignal {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (slot : OccurrenceSlot)
    (cell : Cell) : Bool :=
  variableConnectorLiteralSignal
    (assignment atom cell)
    (occurrencePolarity source atom slot)

/-- Source truth value presented at one clause terminal.  Missing terminals,
including the third terminal of a binary clause, carry `false`. -/
def sourceTerminalSignal {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) : Bool :=
  match literalAt source clauseIndex
      (literalIndexOfTerminalGroup group) with
  | none => false
  | some literal =>
      PeriodicOneInThree.literalTruth assignment cell literal

/-- Canonical selection of every translated triple in the assembled typed
instance. -/
def matchingOfAssignment {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    (problem source).MatchingAssignment
  | .ordinary atom slot _ triple, cell =>
      variableOccurrenceSelection
        (occurrenceSignal source assignment atom slot cell) triple
  | .fixedRed atom slot triple, cell =>
      fixedRedConnectorSelection
        (!occurrenceSignal source assignment atom slot cell) triple
  | .clause clauseIndex set, cell =>
      x3cClauseCoreSelection
        (sourceTerminalSignal source assignment cell clauseIndex .top)
        (sourceTerminalSignal source assignment cell clauseIndex .left)
        (sourceTerminalSignal source assignment cell clauseIndex .right)
        set

@[simp]
theorem matchingOfAssignment_ordinary
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple) (cell : Cell) :
    matchingOfAssignment source assignment
        (.ordinary atom slot variant triple) cell =
      variableOccurrenceSelection
        (occurrenceSignal source assignment atom slot cell) triple := by
  rfl

@[simp]
theorem matchingOfAssignment_fixedRed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (slot : OccurrenceSlot)
    (triple : FixedRedConnectorTriple) (cell : Cell) :
    matchingOfAssignment source assignment
        (.fixedRed atom slot triple) cell =
      fixedRedConnectorSelection
        (!occurrenceSignal source assignment atom slot cell) triple := by
  rfl

@[simp]
theorem matchingOfAssignment_clause
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (clauseIndex : Nat) (set : X3CClauseSet) (cell : Cell) :
    matchingOfAssignment source assignment
        (.clause clauseIndex set) cell =
      x3cClauseCoreSelection
        (sourceTerminalSignal source assignment cell clauseIndex .top)
        (sourceTerminalSignal source assignment cell clauseIndex .left)
        (sourceTerminalSignal source assignment cell clauseIndex .right)
        set := by
  rfl

/-- The canonical ordinary occurrence module covers all of its private
elements. -/
theorem matchingOfAssignment_ordinary_holds
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant) (cell : Cell) :
    VariableOccurrenceHolds fun triple =>
      matchingOfAssignment source assignment
        (.ordinary atom slot variant triple) cell := by
  change VariableOccurrenceHolds
    (variableOccurrenceSelection
      (occurrenceSignal source assignment atom slot cell))
  cases occurrenceSignal source assignment atom slot cell <;>
    native_decide

/-- The canonical fixed-red detour covers all eight private elements. -/
theorem matchingOfAssignment_fixedRed_holds
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (slot : OccurrenceSlot) (cell : Cell) :
    FixedRedConnectorHolds fun triple =>
      matchingOfAssignment source assignment
        (.fixedRed atom slot triple) cell := by
  change FixedRedConnectorHolds
    (fixedRedConnectorSelection
      (!occurrenceSignal source assignment atom slot cell))
  cases occurrenceSignal source assignment atom slot cell <;>
    native_decide

/-- At a genuine occurrence, the connector signal is exactly the signed
source literal's truth value. -/
theorem occurrenceSignal_eq_literalTruth
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (atom : Variable)
    (slot : OccurrenceSlot) (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrenceSignal source assignment atom slot
        (Cell.add translate tagged.1.offset) =
      PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  have atomEq :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup).2
  subst atom
  simp [occurrenceSignal, occurrencePolarity, lookup,
    variableConnectorLiteralSignal,
    PeriodicOneInThree.literalTruth]

/-- The canonical clause-core selection realizes any exact-one triple of
terminal signals. -/
theorem matchingOfAssignment_clause_holds
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (exactlyOne :
      PeriodicOneInThree.ExactlyOne
        [sourceTerminalSignal source assignment cell clauseIndex .top,
          sourceTerminalSignal source assignment cell clauseIndex .left,
          sourceTerminalSignal source assignment cell clauseIndex .right]) :
    X3CClauseCoreHolds
      (fun set =>
        matchingOfAssignment source assignment
          (.clause clauseIndex set) cell)
      (x3cClauseExternalAssignment
        (sourceTerminalSignal source assignment cell clauseIndex .top)
        (sourceTerminalSignal source assignment cell clauseIndex .left)
        (sourceTerminalSignal source assignment cell clauseIndex .right)) := by
  simpa using
    x3cClauseCoreSelection_holds
      (sourceTerminalSignal source assignment cell clauseIndex .top)
      (sourceTerminalSignal source assignment cell clauseIndex .left)
      (sourceTerminalSignal source assignment cell clauseIndex .right)
      exactlyOne

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
