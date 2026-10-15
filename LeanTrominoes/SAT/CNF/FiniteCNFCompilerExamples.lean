/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFCompiler

/-! # Ordinary CNF compiler boundary checks -/
namespace LeanTrominoes.FiniteCNFCompiler
open PeriodicCNF

def trueRequest : Request := ⟨.constant true,0,by trivial⟩
def falseRequest : Request := ⟨.constant false,0,by trivial⟩
def conflictRequest : Request :=
  ⟨.and (.wire ⟨.current,0⟩) (.not (.wire ⟨.next,0⟩)),1,by simp [TransitionExpr.AtomsBelow]⟩

example : FiniteCNF.Satisfiable trueRequest.compile := by
  apply (Request.correct _).mpr
  exact ⟨fun _ => false,rfl⟩

example : ¬FiniteCNF.Satisfiable falseRequest.compile := by
  rw [Request.correct]
  simp [falseRequest,TransitionExpr.eval]

/-- Both endpoints denote the same ordinary variable in this compiler. -/
example : ¬FiniteCNF.Satisfiable conflictRequest.compile := by
  rw [Request.correct]
  simp [conflictRequest,TransitionExpr.eval,TransitionWire.value]

example : decodeFields (fields trueRequest.compile)=some trueRequest.compile := decodeFields_fields _

end LeanTrominoes.FiniteCNFCompiler
