/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPRequestEmitter

/-! # Cook–Levin: actual polynomial-time reductions to finite 3CNF SAT

Every verifier-defined NP language reduces by a finite-alphabet polynomial-time
Turing machine to an ordinary finite formula whose clauses have width at most
three. Both request generation and the structural CNF backend are verified
machines; no running-time claim is inferred from output size.
-/
noncomputable section
namespace LeanTrominoes
namespace Complexity.VerifierInPolyTime
open Computability Turing
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (verifier : VerifierInPolyTime encoding language)

def finiteCNFComputableInPolyTime :
    TM2ComputableInPolyTime encoding.encode FiniteCNFCompiler.finEncoding.encode
      (fun input => (separatedRequest verifier input).compile) :=
  TM2CompositionMachine.computableInPolyTime
    (FiniteNPRequestEmitter.computableInPolyTime verifier) FiniteCNFCompiler.computableInPolyTime

include verifier in
theorem finiteCNFReduction :
    PolyTimeManyOneReducible encoding FiniteCNFCompiler.finEncoding language FiniteCNF.Satisfiable :=
  PolyTimeManyOneReducible.of_computableInPolyTime
    (fun input => (separatedRequest verifier input).compile)
    ⟨finiteCNFComputableInPolyTime verifier⟩
    (fun input => (separatedRequest_correct verifier input).symm)

end Complexity.VerifierInPolyTime

namespace FiniteCNF
open Complexity

def ThreeSatisfiable (formula : Formula Nat) : Prop :=
  WidthAtMost 3 formula ∧ Satisfiable formula

theorem satisfiable_npHard : NPHard FiniteCNFCompiler.finEncoding Satisfiable := by
  intro Input encoding language member
  obtain ⟨verifier⟩ := member
  exact verifier.finiteCNFReduction

theorem threeSatisfiable_npHard : NPHard FiniteCNFCompiler.finEncoding ThreeSatisfiable := by
  intro Input encoding language member
  obtain ⟨verifier⟩ := member
  apply PolyTimeManyOneReducible.of_computableInPolyTime
    (fun input => (verifier.separatedRequest input).compile)
    ⟨verifier.finiteCNFComputableInPolyTime⟩
  intro input
  exact ⟨fun truth => ⟨verifier.separatedRequest_width input,
    (verifier.separatedRequest_correct input).mpr truth⟩,
    fun truth => (verifier.separatedRequest_correct input).mp truth.2⟩

end FiniteCNF
end LeanTrominoes
