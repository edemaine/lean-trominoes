/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Polynomial-time preparation of compact carrier-key emitter inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

open Computability Turing

def routeTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Token :=
  tokens.flatMap routeBlock

def activationTokens (actives : List Bool) : List Token :=
  actives.map .activation

/-- Prepare a compact emitter input from two independently compiled views of
one finite-alphabet source. -/
def preparedFrom {Source : Type}
    (descriptors : List Source → List RouteDescriptorPairFieldTags.Token)
    (actives : List Source → List Bool) (source : List Source) :
    List Token :=
  routeTokens (descriptors source) ++ activationTokens (actives source)

@[simp] theorem preparedFrom_eq_prepared {Source : Type}
    (descriptors : List Source → List RouteDescriptorPairFieldTags.Token)
    (actives : List Source → List Bool) (source : List Source) :
    preparedFrom descriptors actives source =
      prepared (descriptors source) (actives source) :=
  rfl

noncomputable def routeTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id routeTokens := by
  exact FiniteBlockTransducer.computableInPolyTime routeBlock

noncomputable def activationTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id activationTokens := by
  let compiler := FiniteBlockTransducer.computableInPolyTime
    (fun active : Bool => [Token.activation active])
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  intro actives
  have outputEq :
      actives.flatMap (fun active => [Token.activation active]) =
        activationTokens actives := by
    induction actives with
    | nil => rfl
    | cons active actives induction =>
        simp [activationTokens, induction]
  have run := compiler.outputsFun actives
  rw [outputEq] at run
  exact run

/-- Compact preparation is polynomial-time whenever its descriptor and
activation views are. -/
noncomputable def preparedFromComputableInPolyTime
    {Source : Type} [Fintype Source] [Inhabited Source]
    (descriptors : List Source → List RouteDescriptorPairFieldTags.Token)
    (actives : List Source → List Bool)
    (descriptorCompiler : TM2ComputableInPolyTime id id descriptors)
    (activeCompiler : TM2ComputableInPolyTime id id actives) :
    TM2ComputableInPolyTime id id
      (preparedFrom descriptors actives) := by
  let routes := TM2CompositionMachine.computableInPolyTime
    descriptorCompiler routeTokensComputableInPolyTime
  let activations := TM2CompositionMachine.computableInPolyTime
    activeCompiler activationTokensComputableInPolyTime
  exact TM2ListAppend.nativeComputableInPolyTime routes activations

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
