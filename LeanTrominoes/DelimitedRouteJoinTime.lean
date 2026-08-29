/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTimeBound
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime

/-! # Polynomial-time delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open Computability Turing

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 9 * Polynomial.X

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 9 * length := by
  simp [timePolynomial, Polynomial.eval_mul]

/-- Joining two delimiter-terminated route streams is linear-time in their
separated encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token × List Token) (List Token) InputSymbol Token
      encode id (fun input => joined input.1 input.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl InputSymbol).invFun (encode input))
        (some (List.map (Equiv.refl Token).invFun
          (id (joined input.1 input.2))))
        (totalTime input.1 input.2) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input.1 input.2) }

/-- Two route-token streams compiled from the same source can be joined in
polynomial time. -/
noncomputable def joinedComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (prefixes suffixes : Source → List Token)
    (prefixCompiler :
      @TM2ComputableInPolyTime Source (List Token) SourceSymbol Token
        encodeSource id prefixes)
    (suffixCompiler :
      @TM2ComputableInPolyTime Source (List Token) SourceSymbol Token
        encodeSource id suffixes) :
    @TM2ComputableInPolyTime Source (List Token) SourceSymbol Token
      encodeSource id
      (fun source => joined (prefixes source) (suffixes source)) := by
  let forked : TM2ComputableInPolyTime encodeSource
      (SeparatedProductEncoding.encode id id)
      (fun source => (prefixes source, suffixes source)) :=
    TM2ForkMachine.computableInPolyTime
      prefixCompiler suffixCompiler
  exact TM2CompositionMachine.computableInPolyTime
    (B := List Token × List Token)
    (f := fun source => (prefixes source, suffixes source))
    (g := fun input => joined input.1 input.2)
    forked computableInPolyTime

end LeanTrominoes.DelimitedRouteJoin

end
