/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMEventEffects
import LeanTrominoes.SAT.Horn.HornWordRAMRepresentation

/-! # The invariant within one Horn bucket traversal -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

theorem Chain.uncons {limit links labels pointer r rest}
    (chain : Chain limit links labels pointer (r::rest)) :
    ∃ node, node< limit ∧ pointer=node+1 ∧ labels node=r ∧ Chain limit links labels (links node) rest := by
  cases chain with
  | cons node within rest tail => exact ⟨node,within,rfl,rfl,tail⟩

def tickCounter (input : Input) (counter : Indexed.RuleId input.2 → ℕ) (r : Indexed.RuleId input.2) :=
  Function.update counter r (counter r-1)

def tickStack (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (r : Indexed.RuleId input.2) :=
  if counter r=1 then Indexed.head input.2 r::stack else stack

theorem tick_balance (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (r : Indexed.RuleId input.2) :
    (tickStack input counter stack r).length+(Worklist.positive (tickCounter input counter r)).card=
      stack.length+(Worklist.positive counter).card := by
  have balance := Worklist.tick_balance counter [r]
  by_cases ready : counter r=1 <;> simp [Worklist.tick,ready] at balance <;>
    simp [tickStack,tickCounter,ready] <;> omega

/-- The strict capacity bound comes from popping one item before processing
its bucket. Counter transitions preserve this remaining work potential. -/
structure TickRep (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (events : List (Indexed.RuleId input.2))
    (data : Data) (contents : Tables) : Prop where
  realizes : (Layout.ofInput input).Realizes data.2 contents
  pointers : (Layout.ofInput input).Pointers data
  heads : ∀ r : Indexed.RuleId input.2, contents Slot.heads r.val=atomCode (Indexed.head input.2 r)
  chain : Chain (Indexed.edges input.2).length (contents Slot.links) (contents Slot.edgeRules)
    (data.1 Reg.event) (events.map Fin.val)
  counters : ∀ r : Indexed.RuleId input.2, contents Slot.counters r.val=counter r
  stored : StackRep contents stack.reverse
  top : data.1 Reg.top=stack.length
  capacity : stack.length+(Worklist.positive counter).card< input.2.rules.size
  one : data.1 Reg.one=1
  zero : data.1 Reg.zero=0

end LeanTrominoes.Horn.WordRAM
