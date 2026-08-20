/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite clause-and-variable shape streams -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShape

open UnaryProgramClauseProfile

/-- A finite presentation shape retains ordered clause profiles and one unary
marker per distinct variable, without retaining infinite variable names. -/
inductive Token
  | clause (profile : ClauseProfile)
  | variable
  deriving DecidableEq, Fintype, Inhabited

def clauseProfiles (shape : List Token) : List ClauseProfile :=
  shape.filterMap fun
    | .clause profile => some profile
    | .variable => none

def variableMarkers (shape : List Token) : List Unit :=
  shape.filterMap fun
    | .clause _ => none
    | .variable => some ()

def variableCount (shape : List Token) : Nat :=
  (variableMarkers shape).length

@[simp] theorem clauseProfiles_append (first second : List Token) :
    clauseProfiles (first ++ second) =
      clauseProfiles first ++ clauseProfiles second := by
  simp [clauseProfiles]

@[simp] theorem variableMarkers_append (first second : List Token) :
    variableMarkers (first ++ second) =
      variableMarkers first ++ variableMarkers second := by
  simp [variableMarkers]

@[simp] theorem clauseProfiles_map_clause
    (profiles : List ClauseProfile) :
    clauseProfiles (profiles.map .clause) = profiles := by
  induction profiles <;> simp_all [clauseProfiles]

@[simp] theorem variableMarkers_map_clause
    (profiles : List ClauseProfile) :
    variableMarkers (profiles.map .clause) = [] := by
  induction profiles <;> simp_all [variableMarkers]

@[simp] theorem clauseProfiles_replicate_clause
    (count : Nat) (profile : ClauseProfile) :
    clauseProfiles (List.replicate count (.clause profile)) =
      List.replicate count profile := by
  induction count <;> simp_all [clauseProfiles, List.replicate_succ]

@[simp] theorem variableMarkers_replicate_clause
    (count : Nat) (profile : ClauseProfile) :
    variableMarkers (List.replicate count (.clause profile)) = [] := by
  induction count <;> simp_all [variableMarkers, List.replicate_succ]

@[simp] theorem clauseProfiles_replicate_variable (count : Nat) :
    clauseProfiles (List.replicate count .variable) = [] := by
  induction count <;> simp_all [clauseProfiles, List.replicate_succ]

@[simp] theorem variableMarkers_replicate_variable (count : Nat) :
    variableMarkers (List.replicate count .variable) =
      List.replicate count () := by
  induction count <;> simp_all [variableMarkers, List.replicate_succ]

end FormulaShape
end PeriodicCNF
end LeanTrominoes
