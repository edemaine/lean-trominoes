/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Activity-supported value maps of padded candidates -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v

variable {Source : Type u} {Target : Type v}

/-- Map an active optional value and make support agree exactly with activity. -/
def Candidate.mapActiveValue (project : Source → Target)
    (candidate : Candidate Source) : Candidate Target where
  value := candidate.value.map project
  supported := candidate.value.isSome

@[simp] theorem Candidate.mapActiveValue_value
    (project : Source → Target) (candidate : Candidate Source) :
    (candidate.mapActiveValue project).value = candidate.value.map project :=
  rfl

@[simp] theorem Candidate.mapActiveValue_supported
    (project : Source → Target) (candidate : Candidate Source) :
    (candidate.mapActiveValue project).supported = candidate.value.isSome :=
  rfl

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
