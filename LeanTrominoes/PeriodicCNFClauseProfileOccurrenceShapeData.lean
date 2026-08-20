/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitData
import LeanTrominoes.PeriodicCNFFormulaShapeData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterMachine

/-! # Finite formula shapes after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileOccurrenceShape

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramClauseProfile
open UnaryProgramTokens

def cycleShape (profile : ClauseProfile) : List FormulaShape.Token :=
  List.replicate profile.literals.length
      (.clause ClauseProfileOccurrenceSplit.implicationProfile) ++
    List.replicate profile.literals.length .variable

/-- Copied source clauses, followed by one implication clause and one
distinct-variable marker per source literal. -/
def shape (source : List ClauseProfile) : List FormulaShape.Token :=
  source.map .clause ++ source.flatMap cycleShape

@[simp] theorem clauseProfiles_shape (source : List ClauseProfile) :
    FormulaShape.clauseProfiles (shape source) =
      ClauseProfileOccurrenceSplit.profiles source := by
  unfold shape ClauseProfileOccurrenceSplit.profiles
    ClauseProfileOccurrenceSplit.cycleProfiles
  rw [FormulaShape.clauseProfiles_append,
    FormulaShape.clauseProfiles_map_clause]
  congr 1
  induction source with
  | nil => rfl
  | cons profile source induction =>
      simp [cycleShape, induction]

@[simp] theorem variableCount_shape (source : List ClauseProfile) :
    FormulaShape.variableCount (shape source) =
      (source.map fun profile => profile.literals.length).sum := by
  unfold FormulaShape.variableCount shape
  rw [FormulaShape.variableMarkers_append,
    FormulaShape.variableMarkers_map_clause]
  simp only [List.nil_append]
  induction source with
  | nil => rfl
  | cons profile source induction =>
      simp [cycleShape, induction]

/-- The indexed appender retains every source profile and emits the cycle and
variable markers after the copied-clause prefix. -/
def family : IndexedTemplateEmitter.Family ClauseProfile :=
  fun profile => some
    (List.replicate profile.literals.length (.fixed .clauseMarker) ++
      List.replicate profile.literals.length (.fixed .freshUnit))

@[simp] theorem positionTokens_family (profile : ClauseProfile)
    (position : Nat) :
    positionTokens (family profile).get! position =
      List.replicate profile.literals.length .clauseMarker ++
        List.replicate profile.literals.length .freshUnit := by
  cases profile <;>
    simp [family, ClauseProfile.literals, positionTokens, Recipe.tokens]

@[simp] theorem emittedAux_family (position : Nat)
    (source : List ClauseProfile) :
    emittedAux family position source =
      source.flatMap fun profile =>
        List.replicate profile.literals.length .clauseMarker ++
          List.replicate profile.literals.length .freshUnit := by
  induction source generalizing position with
  | nil => rfl
  | cons profile source induction =>
      rw [emittedAux_cons_some family position profile source
        (List.replicate profile.literals.length (.fixed .clauseMarker) ++
          List.replicate profile.literals.length (.fixed .freshUnit))
        (by rfl)]
      rw [show positionTokens
          (List.replicate profile.literals.length (.fixed .clauseMarker) ++
            List.replicate profile.literals.length (.fixed .freshUnit))
          position =
          List.replicate profile.literals.length .clauseMarker ++
            List.replicate profile.literals.length .freshUnit by
        cases profile <;>
          simp [ClauseProfile.literals, positionTokens, Recipe.tokens]]
      rw [induction]
      rfl

@[simp] theorem emitted_family (source : List ClauseProfile) :
    emitted family source =
      source.flatMap fun profile =>
        List.replicate profile.literals.length .clauseMarker ++
          List.replicate profile.literals.length .freshUnit := by
  exact emittedAux_family 0 source

def decodeItem : ClauseProfile ⊕ Token → List FormulaShape.Token
  | .inl profile => [.clause profile]
  | .inr .clauseMarker =>
      [.clause ClauseProfileOccurrenceSplit.implicationProfile]
  | .inr .freshUnit => [.variable]
  | .inr _ => []

def generatedShape (source : List ClauseProfile) :
    List FormulaShape.Token :=
  (IndexedTemplateEmitterMachine.appendedOutput family source).flatMap
    decodeItem

@[simp] theorem generatedShape_eq (source : List ClauseProfile) :
    generatedShape source = shape source := by
  unfold generatedShape IndexedTemplateEmitterMachine.appendedOutput shape
  rw [emitted_family, List.flatMap_append, List.flatMap_map,
    List.flatMap_map]
  congr 1
  · induction source <;> simp_all [decodeItem]
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro profile _
    cases profile <;>
      simp [ClauseProfile.literals, cycleShape, decodeItem]

end ClauseProfileOccurrenceShape
end PeriodicCNF
end LeanTrominoes
