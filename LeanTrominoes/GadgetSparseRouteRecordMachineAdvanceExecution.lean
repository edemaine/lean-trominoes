/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCopyExecution

/-! # Complement-counter transition executions for route records -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

/-- Move the entire horizontal counter into its complement at east wrap. -/
def wrapEast_evalsInTime (color : Gadget.WireColor)
    (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word) :
    EvalsToInTime (TM2.step program)
      (wrapEastCfg color .east data)
      (some (scanOutgoingCfg color .east
        { data with
          horizontal := []
          horizontalComplement := word.reverse ++
            data.horizontalComplement }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_wrapEast_nil data color horizontalEq)
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          horizontal := word
          horizontalComplement := () :: data.horizontalComplement }
      have first := oneStep
        (step_wrapEast_cons data color word horizontalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (wrapEastCfg color .east data) (wrapEastCfg color .east nextData)
        (some (scanOutgoingCfg color .east
          { nextData with
            horizontal := []
            horizontalComplement := word.reverse ++
              nextData.horizontalComplement })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Move the entire complement into the horizontal counter at west wrap. -/
def wrapWest_evalsInTime (color : Gadget.WireColor)
    (word : List Unit) (data : TapeData)
    (complementEq : data.horizontalComplement = word) :
    EvalsToInTime (TM2.step program)
      (wrapWestCfg color .west data)
      (some (scanOutgoingCfg color .west
        { data with
          horizontal := word.reverse ++ data.horizontal
          horizontalComplement := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_wrapWest_nil data color complementEq)
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          horizontal := () :: data.horizontal
          horizontalComplement := word }
      have first := oneStep
        (step_wrapWest_cons data color word complementEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (wrapWestCfg color .west data) (wrapWestCfg color .west nextData)
        (some (scanOutgoingCfg color .west
          { nextData with
            horizontal := word.reverse ++ nextData.horizontal
            horizontalComplement := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Exact transition allowance; only horizontal wrap scans a full unary
counter. -/
def advanceTime (location : ComplementLocation) : AxisDirection → Nat
  | .east =>
      if location.horizontalComplement = 0 then
        location.horizontal + 2
      else
        1
  | .west =>
      if location.horizontal = 0 then
        location.horizontalComplement + 2
      else
        1
  | .north | .south | .invalid => 1

@[simp] theorem negativeNatStep_toNat (value : Nat) :
    ((-1 : Int) + -(value : Int)).toNat = 0 := by
  exact Int.toNat_of_nonpos (by omega)

@[simp] theorem natCast_add_two_toNat (value : Nat) :
    ((value : Int) + 1 + 1).toNat = value + 2 := by
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (by omega)]
  push_cast
  omega

@[simp] theorem negSucc_succ_add_one_toNat (value : Nat) :
    (Int.negSucc (value + 1) + 1).toNat = 0 := by
  exact Int.toNat_of_nonpos (by omega)

/-- The finite counter program implements exactly one semantic complement
location transition. -/
def advance_evalsInTime (color : Gadget.WireColor)
    (direction : AxisDirection) (state : State)
    (input : List InputToken) (location : ComplementLocation)
    (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step program)
      (advanceCfg color direction state
        (locationData input location outputReverse output))
      (some (scanOutgoingCfg color direction
        (locationData input (advanceComplementLocation location direction)
          outputReverse output)))
      (advanceTime location direction) := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases direction with
  | east =>
      cases complement with
      | zero =>
          let initial := locationData input
            ⟨horizontal, 0, vertical⟩ outputReverse output
          have first := oneStep
            (step_advance_east_nil state initial color (by
              simp [initial, locationData]))
          let wrapped : TapeData :=
            { initial with horizontalComplement := [] }
          have rest := wrapEast_evalsInTime color
            (List.replicate horizontal ()) wrapped (by
              simp [wrapped, initial, locationData])
          have whole := EvalsToInTime.trans (TM2.step program)
            1 (horizontal + 1)
            (advanceCfg color .east state initial)
            (wrapEastCfg color .east wrapped)
            (some (scanOutgoingCfg color .east
              { wrapped with
                horizontal := []
                horizontalComplement :=
                  (List.replicate horizontal ()).reverse ++
                    wrapped.horizontalComplement })) first
              (by simpa using rest)
          convert whole using 1 <;>
            simp [initial, wrapped, locationData,
              advanceComplementLocation, advanceTime]
      | succ complement =>
          have step := oneStep (step_advance_east_cons state
            (locationData input ⟨horizontal, complement + 1, vertical⟩
              outputReverse output)
            color (List.replicate complement ()) (by
              simp [locationData, List.replicate_succ]))
          convert step using 1 <;>
            simp [locationData, advanceComplementLocation, advanceTime,
              List.replicate_succ]
  | west =>
      cases horizontal with
      | zero =>
          let initial := locationData input
            ⟨0, complement, vertical⟩ outputReverse output
          have first := oneStep
            (step_advance_west_nil state initial color (by
              simp [initial, locationData]))
          let wrapped : TapeData := { initial with horizontal := [] }
          have rest := wrapWest_evalsInTime color
            (List.replicate complement ()) wrapped (by
              simp [wrapped, initial, locationData])
          have whole := EvalsToInTime.trans (TM2.step program)
            1 (complement + 1)
            (advanceCfg color .west state initial)
            (wrapWestCfg color .west wrapped)
            (some (scanOutgoingCfg color .west
              { wrapped with
                horizontal := (List.replicate complement ()).reverse ++
                  wrapped.horizontal
                horizontalComplement := [] })) first
              (by simpa using rest)
          convert whole using 1 <;>
            simp [initial, wrapped, locationData,
              advanceComplementLocation, advanceTime]
      | succ horizontal =>
          have step := oneStep (step_advance_west_cons state
            (locationData input ⟨horizontal + 1, complement, vertical⟩
              outputReverse output)
            color (List.replicate horizontal ()) (by
              simp [locationData, List.replicate_succ]))
          convert step using 1 <;>
            simp [locationData, advanceComplementLocation, advanceTime,
              List.replicate_succ]
  | north =>
      cases vertical with
      | ofNat vertical =>
          cases vertical with
          | zero =>
              have step := oneStep (step_advance_north_nonpositive state
                (locationData input ⟨horizontal, complement, 0⟩
                  outputReverse output) color (by
                    simp [locationData, signedPositive]))
              convert step using 1 <;>
                simp [locationData, signedPositive, signedNegative,
                  advanceComplementLocation, advanceTime]
          | succ vertical =>
              have step := oneStep (step_advance_north_positive state
                (locationData input
                  ⟨horizontal, complement, Int.ofNat (vertical + 1)⟩
                  outputReverse output)
                color (List.replicate vertical ()) (by
                  simp [locationData, signedPositive,
                    List.replicate_succ]))
              convert step using 1 <;>
                simp [locationData, signedPositive, signedNegative,
                  advanceComplementLocation, advanceTime,
                  List.replicate_succ]
      | negSucc vertical =>
          have step := oneStep (step_advance_north_nonpositive state
            (locationData input ⟨horizontal, complement, Int.negSucc vertical⟩
              outputReverse output) color (by
                simp [locationData, signedPositive]))
          convert step using 1 <;>
            simp [locationData, signedPositive, signedNegative,
              advanceComplementLocation, advanceTime,
              List.replicate_succ]
  | south =>
      cases vertical with
      | ofNat vertical =>
          have step := oneStep (step_advance_south_nonnegative state
            (locationData input ⟨horizontal, complement, Int.ofNat vertical⟩
              outputReverse output) color (by
                simp [locationData, signedNegative]))
          convert step using 1 <;>
            simp [locationData, signedPositive, signedNegative,
              advanceComplementLocation, advanceTime,
              List.replicate_succ]
      | negSucc vertical =>
          have step := oneStep (step_advance_south_negative state
            (locationData input ⟨horizontal, complement, Int.negSucc vertical⟩
              outputReverse output)
            color (List.replicate vertical ()) (by
              simp [locationData, signedNegative,
                List.replicate_succ]))
          cases vertical <;>
            convert step using 1 <;>
              simp [locationData, signedPositive, signedNegative,
                advanceComplementLocation, advanceTime,
                List.replicate_succ]
  | invalid =>
      have step := oneStep (step_advance_invalid state
        (locationData input ⟨horizontal, complement, vertical⟩
          outputReverse output) color)
      convert step using 1 <;>
        simp [locationData, advanceComplementLocation, advanceTime]

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
