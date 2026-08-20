/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineData

/-! # Exact finite literal profiles through the Figure 9 transformations -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseProfile

def negateProfile (profile : LiteralProfile) : LiteralProfile :=
  { profile with value := !profile.value }

def anchoredProfile (anchor : LiteralProfile) (value : Bool) :
    LiteralProfile :=
  { nextSlice := anchor.nextSlice, value := value }

/-- Exact profiles emitted by the Figure 9 disjunction gadget, including its
padding unit clauses.  Every auxiliary is located at the first source
literal's periodic anchor. -/
def oneInThreeProfiles : ClauseProfile → List ClauseProfile
  | .unary first =>
      let positive := anchoredProfile first true
      let negative := anchoredProfile first false
      [.ternary first positive positive,
        .ternary negative positive positive,
        .ternary negative positive positive,
        .unary negative,
        .unary negative]
  | .binary first second =>
      let positive := anchoredProfile first true
      let negative := anchoredProfile first false
      [.ternary first positive positive,
        .ternary (negateProfile second) positive positive,
        .ternary negative positive positive,
        .unary negative]
  | .ternary first second third =>
      let positive := anchoredProfile first true
      [.ternary first positive positive,
        .ternary (negateProfile second) positive positive,
        .ternary (negateProfile third) positive positive]

/-- Exact profile expansion of one exact-one clause during unit removal. -/
def noUnitProfiles : ClauseProfile → List ClauseProfile
  | .unary literal =>
      let positive := anchoredProfile literal true
      [.ternary (negateProfile literal) positive positive,
        .binary positive positive]
  | .binary first second => [.binary first second]
  | .ternary first second third => [.ternary first second third]

/-- Exact unit-free profile block produced from one guarded source clause. -/
def clauseProfiles (profile : ClauseProfile) : List ClauseProfile :=
  (oneInThreeProfiles profile).flatMap noUnitProfiles

/-- Complete exact profile stream after both Figure 9 transformations. -/
def profiles (source : List ClauseProfile) : List ClauseProfile :=
  source.flatMap clauseProfiles

@[simp] theorem oneInThreeProfiles_map_arity (profile : ClauseProfile) :
    (oneInThreeProfiles profile).map ClauseProfile.arity =
      oneInThreeArities profile := by
  cases profile <;> rfl

@[simp] theorem noUnitProfiles_map_arity (profile : ClauseProfile) :
    (noUnitProfiles profile).map ClauseProfile.arity =
      noUnitArities profile.arity := by
  cases profile <;> rfl

@[simp] theorem clauseProfiles_map_arity (profile : ClauseProfile) :
    (clauseProfiles profile).map ClauseProfile.arity =
      clauseArities profile := by
  cases profile <;> rfl

/-- Forgetting literal data recovers the previously certified final arity
stream. -/
@[simp] theorem profiles_map_arity (source : List ClauseProfile) :
    (profiles source).map ClauseProfile.arity = arities source := by
  unfold profiles arities clauseProfiles clauseArities
  induction source with
  | nil => rfl
  | cons profile source induction =>
      simp only [List.flatMap_cons, List.map_append, induction]
      cases profile <;> rfl

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
