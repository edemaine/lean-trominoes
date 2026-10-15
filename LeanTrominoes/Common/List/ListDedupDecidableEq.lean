/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Independence of list deduplication from equality-decider choice -/

namespace LeanTrominoes

/-- Proof irrelevance makes `List.dedup` independent of which correct
decidable-equality implementation is selected. -/
theorem listDedup_eq_of_decidableEq
    {Alpha : Type} (first second : DecidableEq Alpha)
    (values : List Alpha) :
    @List.dedup Alpha first values = @List.dedup Alpha second values := by
  have equal : first = second := Subsingleton.elim _ _
  subst second
  rfl

end LeanTrominoes
