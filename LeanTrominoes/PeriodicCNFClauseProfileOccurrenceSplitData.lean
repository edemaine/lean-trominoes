/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterMachine
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite clause-profile occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileOccurrenceSplit

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramClauseProfile
open UnaryProgramTokens

/-- Every occurrence-cycle clause has this route-relevant profile. -/
def implicationProfile : ClauseProfile :=
  .binary (current false) (current true)

def cycleProfiles (profiles : List ClauseProfile) : List ClauseProfile :=
  profiles.flatMap fun profile =>
    List.replicate profile.literals.length implicationProfile

@[simp] theorem cycleProfiles_eq_replicate
    (source : List ClauseProfile) :
    cycleProfiles source =
      List.replicate
        (source.map fun profile => profile.literals.length).sum
        implicationProfile := by
  induction source with
  | nil => rfl
  | cons profile source induction =>
      change List.replicate profile.literals.length implicationProfile ++
          cycleProfiles source =
        List.replicate
          (profile.literals.length +
            (source.map fun profile => profile.literals.length).sum)
          implicationProfile
      rw [induction, List.replicate_add]

/-- Occurrence splitting keeps the source clauses first and appends one
binary implication clause per source literal. -/
def profiles (source : List ClauseProfile) : List ClauseProfile :=
  source ++ cycleProfiles source

/-- One input profile emits one fixed marker per literal. -/
def cycleFamily : IndexedTemplateEmitter.Family ClauseProfile :=
  fun profile => some
    (List.replicate profile.literals.length (.fixed .clauseMarker))

@[simp] theorem positionTokens_cycleFamily
    (profile : ClauseProfile) (position : Nat) :
    positionTokens (cycleFamily profile).get! position =
      List.replicate profile.literals.length .clauseMarker := by
  cases profile <;>
    simp [cycleFamily, ClauseProfile.literals, positionTokens,
      Recipe.tokens]

@[simp] theorem emittedAux_cycleFamily (position : Nat)
    (source : List ClauseProfile) :
    emittedAux cycleFamily position source =
      (cycleProfiles source).map fun _ => .clauseMarker := by
  induction source generalizing position with
  | nil => rfl
  | cons profile source induction =>
      rw [emittedAux_cons_some cycleFamily position profile source
        (List.replicate profile.literals.length (.fixed .clauseMarker))
        (by rfl)]
      rw [show positionTokens
          (List.replicate profile.literals.length (.fixed .clauseMarker))
          position =
            List.replicate profile.literals.length .clauseMarker by
        cases profile <;>
          simp [ClauseProfile.literals, positionTokens, Recipe.tokens]]
      rw [induction]
      simp [cycleProfiles, List.map_append]

@[simp] theorem emitted_cycleFamily (source : List ClauseProfile) :
    emitted cycleFamily source =
      (cycleProfiles source).map fun _ => .clauseMarker := by
  exact emittedAux_cycleFamily 0 source

def decodeItem : ClauseProfile ⊕ Token → List ClauseProfile
  | .inl profile => [profile]
  | .inr .clauseMarker => [implicationProfile]
  | .inr _ => []

@[simp] theorem decode_replicate_clauseMarker (count : Nat) :
    (List.replicate count (.clauseMarker : Token)).flatMap
        (fun token => decodeItem (.inr token)) =
      List.replicate count implicationProfile := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.flatMap_cons,
        List.replicate_succ]
      change implicationProfile ::
          (List.replicate count (.clauseMarker : Token)).flatMap
            (fun token => decodeItem (.inr token)) =
        implicationProfile :: List.replicate count implicationProfile
      rw [induction]

/-- Machine-shaped occurrence-split output before semantic transport. -/
def generatedProfiles (source : List ClauseProfile) : List ClauseProfile :=
  (IndexedTemplateEmitterMachine.appendedOutput
    cycleFamily source).flatMap decodeItem

@[simp] theorem generatedProfiles_eq (source : List ClauseProfile) :
    generatedProfiles source = profiles source := by
  unfold generatedProfiles IndexedTemplateEmitterMachine.appendedOutput
    profiles
  rw [emitted_cycleFamily, List.flatMap_append,
    List.flatMap_map, List.flatMap_map]
  have sourceEq :
      source.flatMap (fun profile => decodeItem (.inl profile)) = source := by
    simp [decodeItem]
  rw [sourceEq]
  rw [cycleProfiles_eq_replicate]
  simp only [List.map_replicate]
  rw [decode_replicate_clauseMarker]

end ClauseProfileOccurrenceSplit
end PeriodicCNF
end LeanTrominoes
