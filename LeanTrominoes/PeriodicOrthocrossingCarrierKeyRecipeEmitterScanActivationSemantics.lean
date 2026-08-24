/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanData

/-! # Activation-vector semantics of the compact emitter scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

/-- Shift a stored fixed-length vector across a Boolean word. -/
def scanActives {length : Nat} (stored : List.Vector Bool length)
    (actives : List Bool) : List.Vector Bool length :=
  (FiniteStateTransducer.scan
    (FixedLengthWordEvaluator.transition (Target := Unit))
    stored actives).1

theorem scanState_actives {recipeCount : Nat}
    (state : State recipeCount)
    (input : List CarrierKeyRecipeEmitter.Token) :
    (scanState state input).actives =
      scanActives state.actives
        (CarrierKeyRecipeEmitter.activationBits input) := by
  induction input generalizing state with
  | nil => rfl
  | cons token input induction =>
      cases token with
      | routeUnit side =>
          simpa [scanState, scanToken, scanActives,
            CarrierKeyRecipeEmitter.activationBits, clearPayload]
            using induction (clearPayload state)
      | activation active =>
          simpa [scanState, scanToken, scanActives,
            CarrierKeyRecipeEmitter.activationBits,
            FiniteStateTransducer.scan,
            FixedLengthWordEvaluator.transition]
            using induction
              { actives := FixedLengthWordEvaluator.shiftAppend
                  state.actives active
                payload := none }

theorem scanActives_eq_of_length_eq {length : Nat} (actives : List Bool)
    (lengthEq : actives.length = length) :
    scanActives (List.Vector.replicate length false) actives =
      ⟨actives, lengthEq⟩ := by
  have initialEq : List.Vector.replicate length false =
      FixedLengthWordEvaluator.paddedVector false [] actives
        (by simpa using lengthEq) := by
    apply List.Vector.eq
    simp only [List.Vector.replicate, List.Vector.toList_mk,
      FixedLengthWordEvaluator.paddedVector, List.append_nil]
    rw [lengthEq]
  unfold scanActives
  rw [initialEq, FixedLengthWordEvaluator.scan_paddedVector]
  apply List.Vector.eq
  rfl

@[simp] theorem scanState_initial_actives
    {recipeCount : Nat}
    (input : List CarrierKeyRecipeEmitter.Token)
    (lengthEq : (CarrierKeyRecipeEmitter.activationBits input).length =
      recipeCount) :
    (scanState (initialState recipeCount) input).actives.toList =
      CarrierKeyRecipeEmitter.activationBits input := by
  rw [scanState_actives]
  change (scanActives (List.Vector.replicate recipeCount false)
    (CarrierKeyRecipeEmitter.activationBits input)).toList = _
  rw [scanActives_eq_of_length_eq _ lengthEq]
  rfl

@[simp] theorem scanState_prepared_actives
    {recipeCount : Nat}
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (lengthEq : actives.length = recipeCount) :
    (scanState (initialState recipeCount)
        (CarrierKeyRecipeEmitter.prepared tokens actives)).actives.toList =
      actives := by
  rw [scanState_initial_actives]
  · exact CarrierKeyRecipeEmitter.activationBits_prepared tokens actives
  · rw [CarrierKeyRecipeEmitter.activationBits_prepared]
    exact lengthEq

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
