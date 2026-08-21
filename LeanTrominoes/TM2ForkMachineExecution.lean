/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineOutputExecution

/-! # Complete execution of the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open StateTransition Turing

/-- The fork machine's exact execution before replacing its two output
lengths by polynomial envelopes. -/
def forkRun
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (input : Input) :
    let inputLength := (encodeInput input).length
    let firstOutputLength := (encodeFirst (firstFunction input)).length
    let secondOutputLength := (encodeSecond (secondFunction input)).length
    TM2OutputsInTime (machine first second)
      (encodeInput input)
      (some (physicalSeparated first second
        (List.map first.outputAlphabet.invFun
          (encodeFirst (firstFunction input)))
        (List.map second.outputAlphabet.invFun
          (encodeSecond (secondFunction input)))))
      (4 * firstOutputLength + 4 * secondOutputLength + 7 +
        (second.time.eval inputLength +
          (first.time.eval inputLength + (5 * inputLength + 2)))) := by
  let firstPhysical := List.map first.outputAlphabet.invFun
    (encodeFirst (firstFunction input))
  let secondPhysical := List.map second.outputAlphabet.invFun
    (encodeSecond (secondFunction input))
  let secondInitial := initList second.tm
    (List.map second.inputAlphabet.invFun (encodeInput input))
  let setup := setupRun first second (encodeInput input)
  let firstRun := liftFirstEvalsToInTime first second secondInitial.stk
    (first.outputsFun input)
  let throughFirst := EvalsToInTime.trans (machine first second).step
    (5 * (encodeInput input).length + 2)
    (first.time.eval (encodeInput input).length)
    _ _ _ setup firstRun
  let secondRun := liftSecondEvalsToInTime first second
    (haltList first.tm firstPhysical).stk (second.outputsFun input)
  let throughSecond := EvalsToInTime.trans (machine first second).step
    (first.time.eval (encodeInput input).length +
      (5 * (encodeInput input).length + 2))
    (second.time.eval (encodeInput input).length)
    _ _ _ throughFirst secondRun
  let assembly := outputAssemblyRun first second firstPhysical secondPhysical
  let whole := EvalsToInTime.trans (machine first second).step
    (second.time.eval (encodeInput input).length +
      (first.time.eval (encodeInput input).length +
        (5 * (encodeInput input).length + 2)))
    (4 * firstPhysical.length + 4 * secondPhysical.length + 7)
    _ _ _ throughSecond assembly
  dsimp only
  unfold TM2OutputsInTime
  simpa [firstPhysical, secondPhysical, secondInitial]
    using whole

end TM2ForkMachine
end LeanTrominoes
