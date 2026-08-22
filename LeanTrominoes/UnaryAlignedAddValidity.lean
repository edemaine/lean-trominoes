/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddInput

/-! # Constructing aligned unary addition promises -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

def Valid.of_length_eq {firsts seconds : List Nat}
    (lengthEq : firsts.length = seconds.length) :
    Valid firsts seconds := by
  induction firsts generalizing seconds with
  | nil =>
      cases seconds with
      | nil => exact .nil
      | cons second seconds => simp at lengthEq
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at lengthEq
      | cons second seconds =>
          exact .cons (induction (by simpa using lengthEq))

end UnaryAlignedAddMachine
end LeanTrominoes
