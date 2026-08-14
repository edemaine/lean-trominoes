/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.TM2CompositionMachine

/-!
# Composition of encoded polynomial-time reductions

The complexity definitions package the finite input and output encodings into
each many-one reduction.  This file records the transitivity theorem obtained
by applying the verified sequential-composition machine to the intermediate
finite alphabet.
-/

noncomputable section

namespace LeanTrominoes
namespace Complexity

open Computability

/-- Polynomial-time many-one reductions compose through their intermediate
finite encoding. -/
theorem PolyTimeManyOneReducible.trans
    {α β γ : Type}
    {encodingA : FinEncoding α}
    {encodingB : FinEncoding β}
    {encodingC : FinEncoding γ}
    {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    (first : PolyTimeManyOneReducible encodingA encodingB p q)
    (second : PolyTimeManyOneReducible encodingB encodingC q r) :
    PolyTimeManyOneReducible encodingA encodingC p r := by
  obtain ⟨reduceFirst, ⟨firstComputer⟩, firstCorrect⟩ := first
  obtain ⟨reduceSecond, ⟨secondComputer⟩, secondCorrect⟩ := second
  letI : Fintype encodingB.Γ := encodingB.ΓFin
  refine ⟨fun input => reduceSecond (reduceFirst input), ?_, ?_⟩
  · exact ⟨TM2CompositionMachine.computableInPolyTime
      firstComputer secondComputer⟩
  · intro input
    exact (firstCorrect input).trans (secondCorrect (reduceFirst input))

end Complexity
end LeanTrominoes
