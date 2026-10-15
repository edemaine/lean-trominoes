/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteTransitionExpression
namespace LeanTrominoes.FiniteCNF.Examples
open PeriodicCNF

def toggle : TransitionExpr :=
  .and (.or (.wire ⟨.current,0⟩) (.wire ⟨.next,0⟩))
    (.or (.not (.wire ⟨.current,0⟩)) (.not (.wire ⟨.next,0⟩)))

-- Two transitions return to the original bit; the endpoint is time 2.
example : Satisfiable (boundedExpression toggle 1 2 [(0,false)] [(0,false)]) := by
  apply (boundedExpression_correct toggle 1 2 _ _ (by simp [toggle,TransitionExpr.AtomsBelow])
    (by simp) (by simp)).mpr
  refine ⟨fun time _ => decide (time=1),by simp [Pinned],?_,by simp [Pinned]⟩
  intro time ht
  have h : time=0 ∨ time=1 := by omega
  rcases h with rfl|rfl <;> decide

-- A single transition cannot both flip the bit and leave it unchanged.
example : ¬Satisfiable (boundedExpression toggle 1 1 [(0,false)] [(0,false)]) := by
  intro sat
  obtain ⟨trace,first,step,last⟩ := (boundedExpression_correct toggle 1 1 _ _
    (by simp [toggle,TransitionExpr.AtomsBelow]) (by simp) (by simp)).mp sat
  have a : trace 0 0=false := first (0,false) (by simp)
  have b : trace 1 0=false := last (0,false) (by simp)
  have h := step 0 (by omega)
  simp [toggle,TransitionExpr.eval,TransitionWire.value,a,b] at h

-- Zero steps identify initial and final states, without adding a wrap edge.
example : ¬Satisfiable (boundedExpression (.constant true) 1 0 [(0,false)] [(0,true)]) := by
  intro sat
  obtain ⟨trace,first,_,last⟩ := (boundedExpression_correct (.constant true) 1 0 _ _
    (by trivial) (by simp) (by simp)).mp sat
  have a : trace 0 0=false := first (0,false) (by simp)
  have b : trace 0 0=true := last (0,true) (by simp)
  simp [a] at b

end LeanTrominoes.FiniteCNF.Examples
