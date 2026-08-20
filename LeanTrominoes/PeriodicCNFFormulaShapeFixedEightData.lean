/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitData
import LeanTrominoes.PeriodicCNFFormulaShapeData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterMachine

/-! # Finite formula shapes after fixed-eight occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEight

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramClauseProfile
open UnaryProgramTokens

/-- Eight compass copies and one separator copy belong to every source
variable. -/
def copiesPerVariable : Nat := 9

/-- One fixed implication ring and its nine distinct output variables. -/
def cycleShape : List FormulaShape.Token :=
  List.replicate copiesPerVariable
      (.clause ClauseProfileOccurrenceSplit.implicationProfile) ++
    List.replicate copiesPerVariable .variable

@[simp] theorem clauseProfiles_cycleShape :
    FormulaShape.clauseProfiles cycleShape =
      List.replicate copiesPerVariable
        ClauseProfileOccurrenceSplit.implicationProfile := by
  simp [cycleShape]

@[simp] theorem variableMarkers_cycleShape :
    FormulaShape.variableMarkers cycleShape =
      List.replicate copiesPerVariable () := by
  simp [cycleShape]

/-- Copied source clauses followed by one fixed nine-copy ring per incoming
distinct-variable marker. -/
def shape (source : List FormulaShape.Token) : List FormulaShape.Token :=
  (FormulaShape.clauseProfiles source).map .clause ++
    source.flatMap fun
      | .clause _ => []
      | .variable => cycleShape

/-- The implication-profile suffix contains one fixed block per incoming
variable marker. -/
def cycleProfiles (source : List FormulaShape.Token) : List ClauseProfile :=
  (FormulaShape.variableMarkers source).flatMap fun _ =>
    List.replicate copiesPerVariable
      ClauseProfileOccurrenceSplit.implicationProfile

private theorem flatMap_replicate_eq_replicate
    {Item : Type*} (items : List Item) (profile : ClauseProfile) :
    (items.flatMap fun _ =>
      List.replicate copiesPerVariable profile) =
      List.replicate (copiesPerVariable * items.length) profile := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      rw [List.flatMap_cons, induction, ← List.replicate_add]
      congr 1
      simp only [List.length_cons]
      unfold copiesPerVariable
      omega

@[simp] theorem cycleProfiles_eq_replicate
    (source : List FormulaShape.Token) :
    cycleProfiles source =
      List.replicate
        (copiesPerVariable * FormulaShape.variableCount source)
        ClauseProfileOccurrenceSplit.implicationProfile := by
  unfold cycleProfiles FormulaShape.variableCount
  exact flatMap_replicate_eq_replicate
    (FormulaShape.variableMarkers source)
    ClauseProfileOccurrenceSplit.implicationProfile

private theorem clauseProfiles_cycles
    (source : List FormulaShape.Token) :
    FormulaShape.clauseProfiles
        (source.flatMap fun
          | .clause _ => []
          | .variable => cycleShape) =
      cycleProfiles source := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, FormulaShape.clauseProfiles_append]
      cases token with
      | clause profile =>
          simpa [cycleProfiles, FormulaShape.clauseProfiles,
            FormulaShape.variableMarkers] using induction
      | «variable» =>
          rw [clauseProfiles_cycleShape, induction]
          rfl

def cycleVariableMarkers (source : List FormulaShape.Token) : List Unit :=
  (FormulaShape.variableMarkers source).flatMap fun _ =>
    List.replicate copiesPerVariable ()

private theorem variableMarkers_cycles
    (source : List FormulaShape.Token) :
    FormulaShape.variableMarkers
        (source.flatMap fun
          | .clause _ => []
          | .variable => cycleShape) =
      cycleVariableMarkers source := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, FormulaShape.variableMarkers_append]
      cases token with
      | clause profile =>
          simpa [cycleVariableMarkers,
            FormulaShape.variableMarkers] using induction
      | «variable» =>
          rw [variableMarkers_cycleShape, induction]
          rfl

private theorem length_replicatedBlocks (markers : List Unit) :
    (markers.flatMap fun _ =>
      List.replicate copiesPerVariable ()).length =
      copiesPerVariable * markers.length := by
  induction markers with
  | nil => rfl
  | cons marker markers induction =>
      simp [induction, Nat.mul_succ, Nat.add_comm]

@[simp] theorem clauseProfiles_shape
    (source : List FormulaShape.Token) :
    FormulaShape.clauseProfiles (shape source) =
      FormulaShape.clauseProfiles source ++
        cycleProfiles source := by
  rw [shape, FormulaShape.clauseProfiles_append,
    FormulaShape.clauseProfiles_map_clause, clauseProfiles_cycles]

@[simp] theorem variableCount_shape
    (source : List FormulaShape.Token) :
    FormulaShape.variableCount (shape source) =
      copiesPerVariable * FormulaShape.variableCount source := by
  unfold FormulaShape.variableCount shape
  rw [FormulaShape.variableMarkers_append,
    FormulaShape.variableMarkers_map_clause,
    List.nil_append, variableMarkers_cycles]
  exact length_replicatedBlocks (FormulaShape.variableMarkers source)

/-- The indexed appender emits one complete fixed ring only for a source
variable marker. -/
def family : IndexedTemplateEmitter.Family FormulaShape.Token
  | .clause _ => none
  | .variable => some
      (List.replicate copiesPerVariable (.fixed .clauseMarker) ++
        List.replicate copiesPerVariable (.fixed .freshUnit))

@[simp] theorem positionTokens_family (token : FormulaShape.Token)
    (position : Nat) :
    positionTokens ((family token).getD []) position =
      match token with
      | .clause _ => []
      | .variable =>
          List.replicate copiesPerVariable Token.clauseMarker ++
            List.replicate copiesPerVariable Token.freshUnit := by
  cases token <;>
    simp [family, positionTokens, Recipe.tokens, copiesPerVariable]

@[simp] theorem emittedAux_family (position : Nat)
    (source : List FormulaShape.Token) :
    emittedAux family position source =
      source.flatMap fun
        | .clause _ => []
        | .variable =>
            List.replicate copiesPerVariable .clauseMarker ++
              List.replicate copiesPerVariable .freshUnit := by
  induction source generalizing position with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [emittedAux_cons_none family position (.clause profile)
            source (by rfl), induction position]
          rfl
      | «variable» =>
          rw [emittedAux_cons_some family position .variable source
            (List.replicate copiesPerVariable (.fixed .clauseMarker) ++
              List.replicate copiesPerVariable (.fixed .freshUnit))
            (by rfl)]
          rw [show positionTokens
              (List.replicate copiesPerVariable (.fixed .clauseMarker) ++
                List.replicate copiesPerVariable (.fixed .freshUnit))
              position =
              List.replicate copiesPerVariable .clauseMarker ++
                List.replicate copiesPerVariable .freshUnit by
            simp [positionTokens, Recipe.tokens, copiesPerVariable]]
          rw [induction]
          rfl

@[simp] theorem emitted_family (source : List FormulaShape.Token) :
    emitted family source =
      source.flatMap fun
        | .clause _ => []
        | .variable =>
            List.replicate copiesPerVariable .clauseMarker ++
              List.replicate copiesPerVariable .freshUnit := by
  exact emittedAux_family 0 source

def decodeItem : FormulaShape.Token ⊕ Token → List FormulaShape.Token
  | .inl (.clause profile) => [.clause profile]
  | .inl .variable => []
  | .inr .clauseMarker =>
      [.clause ClauseProfileOccurrenceSplit.implicationProfile]
  | .inr .freshUnit => [.variable]
  | .inr _ => []

def generatedShape (source : List FormulaShape.Token) :
    List FormulaShape.Token :=
  (IndexedTemplateEmitterMachine.appendedOutput family source).flatMap
    decodeItem

@[simp] theorem generatedShape_eq (source : List FormulaShape.Token) :
    generatedShape source = shape source := by
  unfold generatedShape IndexedTemplateEmitterMachine.appendedOutput shape
  rw [emitted_family, List.flatMap_append, List.flatMap_map]
  congr 1
  · induction source with
    | nil => rfl
    | cons token source induction =>
        cases token <;>
          simpa [decodeItem, FormulaShape.clauseProfiles] using induction
  · rw [List.flatMap_map, List.flatMap_assoc]
    apply List.flatMap_congr
    intro token _
    cases token <;>
      simp [cycleShape, decodeItem, copiesPerVariable]

end FormulaShapeFixedEight
end PeriodicCNF
end LeanTrominoes
