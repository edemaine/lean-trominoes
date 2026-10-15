/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnOrdinalCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnKeyedRelation

/-! # Compiling dense indices by an injective table key -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing
variable {Symbol Row Entry : Type} [Fintype Symbol] [Inhabited Symbol] [DecidableEq Entry]
  {rows : List Symbol → List Row} {entries : List Symbol → List Entry}
  {key : List Symbol → Entry → Nat} {entry : List Symbol → Row → Entry}

def denseLookup
    (queries : Compiler rows (fun s row => key s (entry s row)))
    (keys : Compiler entries key)
    (ordinals : Compiler entries (fun s e => (entries s).idxOf e))
    (injective : ∀ s, Set.InjOn (key s) {e | e ∈ entries s})
    (listed : ∀ s row, row ∈ rows s → entry s row ∈ entries s) :
    Compiler rows (fun s row => (entries s).idxOf (entry s row)) := by
  apply keyedRelation queries keys ordinals
  · intro s first firstMember second secondMember equal
    exact congrArg (fun e => (entries s).idxOf e) (injective s firstMember secondMember equal)
  · intro s row member
    exact ⟨_,listed s row member,rfl⟩
  · intro s row rowMember found foundMember equal
    exact congrArg (fun e => (entries s).idxOf e) (injective s foundMember (listed s row rowMember) equal)

end LeanTrominoes.UnaryColumn
end
