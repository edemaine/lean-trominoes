/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Computability.Primrec.List

/-! # Primitive-recursive finite lookup chains -/

noncomputable section

namespace LeanTrominoes
namespace Computability

/-- A finite lookup chain for a fixed function.  The fallback is observed
only when the queried value is absent from the supplied list. -/
def finiteFunctionTable
    {Alpha Beta : Type*} [DecidableEq Alpha]
    (function : Alpha → Beta) (fallback : Beta) :
    List Alpha → Alpha → Beta
  | [], _ => fallback
  | head :: tail, input =>
      if input = head then function head
      else finiteFunctionTable function fallback tail input

theorem finiteFunctionTable_primrec
    {Alpha Beta : Type*}
    [Primcodable Alpha] [Primcodable Beta] [DecidableEq Alpha]
    (function : Alpha → Beta) (fallback : Beta)
    (values : List Alpha) :
    Primrec (finiteFunctionTable function fallback values) := by
  induction values with
  | nil => exact Primrec.const fallback
  | cons head tail induction =>
      exact Primrec.ite
        (Primrec.eq.comp Primrec.id (Primrec.const head))
        (Primrec.const (function head)) induction

end Computability
end LeanTrominoes
