/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite clause profiles for exact-one polarity normalization -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfilePolarityNormalization

open UnaryProgramClauseProfile

def normalizedPolarity : Nat → Bool
  | 0 | 1 => false
  | _ => true

def withValue (profile : LiteralProfile) (value : Bool) : LiteralProfile :=
  { profile with value := value }

def normalizedLiteral (literalIndex : Nat)
    (profile : LiteralProfile) : LiteralProfile :=
  withValue profile (normalizedPolarity literalIndex)

def complementProfile (profile : LiteralProfile) : ClauseProfile :=
  .binary (withValue profile false) (withValue profile false)

def complementProfiles (literalIndex : Nat)
    (profile : LiteralProfile) : List ClauseProfile :=
  if profile.value =
      normalizedPolarity literalIndex
  then []
  else [complementProfile profile]

/-- One normalized clause followed by its occurrence-local complement
clauses, in literal order. -/
def clauseProfiles : ClauseProfile → List ClauseProfile
  | .unary first =>
      [.unary (normalizedLiteral 0 first)] ++
        complementProfiles 0 first
  | .binary first second =>
      [.binary (normalizedLiteral 0 first)
          (normalizedLiteral 1 second)] ++
        complementProfiles 0 first ++
          complementProfiles 1 second
  | .ternary first second third =>
      [.ternary (normalizedLiteral 0 first)
          (normalizedLiteral 1 second)
          (normalizedLiteral 2 third)] ++
        complementProfiles 0 first ++
          complementProfiles 1 second ++
            complementProfiles 2 third

def profiles (source : List ClauseProfile) : List ClauseProfile :=
  source.flatMap clauseProfiles

/-- Polarity normalization preserves each source clause's arity and adds only
binary complement clauses. -/
theorem clauseProfiles_head_arity (profile : ClauseProfile) :
    (clauseProfiles profile).head?.map ClauseProfile.arity =
      some profile.arity := by
  cases profile <;> rfl

theorem clauseProfiles_tail_all_binary (profile generated : ClauseProfile)
    (member : generated ∈ (clauseProfiles profile).drop 1) :
    generated.arity = .binary := by
  cases profile with
  | unary first =>
      simp [clauseProfiles, complementProfiles, complementProfile] at member
      rcases member with ⟨_, rfl⟩
      rfl
  | binary first second =>
      simp [clauseProfiles, complementProfiles, complementProfile] at member
      rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  | ternary first second third =>
      simp [clauseProfiles, complementProfiles, complementProfile] at member
      rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end ClauseProfilePolarityNormalization
end PeriodicCNF
end LeanTrominoes
