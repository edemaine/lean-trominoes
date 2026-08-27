/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchExecution

/-! # Polynomial envelope for canonical route-request batches -/

namespace LeanTrominoes

open Computability Turing

noncomputable section

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

theorem validRequestOutput_length_le_square (request : ValidRequest) :
    (validRequestOutput request).length ≤
      (validRequestInput request).length ^ 2 := by
  let period := request.1.metadata.period
  let horizontal := request.1.metadata.cursorHorizontal
  let vertical := request.1.metadata.cursorVertical
  let directions := requestDirections request.1
  let length := (validRequestInput request).length
  have lengthEq : length =
      period + horizontal + vertical + directions.length + 5 := by
    simpa [length, validRequestInput, period, horizontal, vertical,
      directions] using normalizedRequestBlock_length request.1
  have periodEq : request.1.metadata.complementLocation.period = period := by
    simpa [period] using
      request.1.metadata.complementLocation_period request.2
  have massEq :
      verticalMass request.1.metadata.complementLocation = vertical := by
    simp [vertical]
  have directionLe : directions.length ≤ length := by omega
  have scaleLe :
      request.1.metadata.complementLocation.period +
          verticalMass request.1.metadata.complementLocation +
          directions.length + 2 ≤ length := by
    rw [periodEq, massEq]
    omega
  have raw := complementRecordBlock_length_le request.1
  change (PeriodicCNFStripReduction.RouteRasterRequest.complementRecordBlock
    request.1).length ≤ length ^ 2
  simpa only [directions, pow_two] using raw.trans
    (Nat.mul_le_mul directionLe scaleLe)

/-- One request, plus its eventual contribution to final output reversal,
fits a uniform quadratic charge. -/
def unitCost (length : Nat) : Nat :=
  (Fintype.card innerCompiler.tm.K + 50) * (length + 1) ^ 2

theorem request_charge_le (request : ValidRequest) :
    requestRunTime request + 2 * (validRequestOutput request).length ≤
      unitCost (validRequestInput request).length := by
  have outputBound := validRequestOutput_length_le_square request
  have bodyLength :
      (validRequestInput request).length =
        (requestBody request).length + 1 := by
    rw [validRequestInput_eq_body]
    simp
  have inputPositive : 1 ≤ (validRequestInput request).length := by
    exact input_length_pos request
  have innerTimeEq :
      innerCompiler.time.eval (validRequestInput request).length =
        16 * ((validRequestInput request).length + 1) ^ 2 := by
    change canonicalTimePolynomial.eval
      (validRequestInput request).length = _
    exact canonicalTimePolynomial_eval _
  unfold requestRunTime blockRunTime unitCost
  rw [innerTimeEq]
  nlinarith [Nat.zero_le (Fintype.card innerCompiler.tm.K),
    Nat.zero_le (requestBody request).length]

theorem unitCost_mono {smaller larger : Nat} (bound : smaller ≤ larger) :
    unitCost smaller ≤ unitCost larger := by
  unfold unitCost
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right bound 1) 2)

theorem request_charge_le_limit (request : ValidRequest) (limit : Nat)
    (bound : (validRequestInput request).length ≤ limit) :
    requestRunTime request + 2 * (validRequestOutput request).length ≤
      unitCost limit :=
  (request_charge_le request).trans (unitCost_mono bound)

/-- Recursive execution is bounded by one uniform charge per remaining
request, plus reversal of the already accumulated output. -/
theorem runTime_le_of_limit (requests : List ValidRequest)
    (outputReverse : List OutputToken) (limit : Nat)
    (bounded : ∀ request ∈ requests,
      (validRequestInput request).length ≤ limit) :
    runTime requests outputReverse ≤
      2 * outputReverse.length + 3 + requests.length * unitCost limit := by
  induction requests generalizing outputReverse with
  | nil => simp [runTime]
  | cons request requests induction =>
      have requestBound := bounded request (by simp)
      have restBound : ∀ other ∈ requests,
          (validRequestInput other).length ≤ limit := by
        intro other member
        exact bounded other (by simp [member])
      have rest := induction
        ((validRequestOutput request).reverse ++ outputReverse) restBound
      have charge := request_charge_le_limit request limit requestBound
      have rest' :
          runTime requests
              ((validRequestOutput request).reverse ++ outputReverse) ≤
            2 * ((validRequestOutput request).length +
                outputReverse.length) +
              3 + requests.length * unitCost limit := by
        simpa using rest
      have charge' :
          2 * (validRequestOutput request).length + requestRunTime request ≤
            unitCost limit := by
        simpa [Nat.add_comm] using charge
      simp only [runTime, List.length_cons]
      calc
        runTime requests
              ((validRequestOutput request).reverse ++ outputReverse) +
            requestRunTime request ≤
          (2 *
                ((validRequestOutput request).length +
                  outputReverse.length) +
              3 + requests.length * unitCost limit) +
            requestRunTime request :=
              Nat.add_le_add_right rest' _
        _ = 2 * outputReverse.length + 3 +
            requests.length * unitCost limit +
              (2 * (validRequestOutput request).length +
                requestRunTime request) := by omega
        _ ≤ 2 * outputReverse.length + 3 +
            requests.length * unitCost limit + unitCost limit :=
              Nat.add_le_add_left charge' _
        _ = 2 * outputReverse.length + 3 +
            (requests.length + 1) * unitCost limit := by ring

theorem member_input_length_le (requests : List ValidRequest)
    {request : ValidRequest} (member : request ∈ requests) :
    (validRequestInput request).length ≤ (input requests).length := by
  unfold input
  induction requests with
  | nil => simp at member
  | cons first requests induction =>
      simp only [List.mem_cons] at member
      rw [List.flatMap_cons, List.length_append]
      rcases member with rfl | member
      · omega
      · exact (induction member).trans (by omega)

theorem initialRunTime_le (requests : List ValidRequest) :
    runTime requests [] ≤
      ((input requests).length + 1) *
        (unitCost (input requests).length + 3) := by
  let length := (input requests).length
  have bounded : ∀ request ∈ requests,
      (validRequestInput request).length ≤ length := by
    intro request member
    exact member_input_length_le requests member
  have raw := runTime_le_of_limit requests [] length bounded
  have count := requests_length_le_input_length requests
  simp only [List.length_nil, mul_zero, zero_add] at raw
  change runTime requests [] ≤ (length + 1) * (unitCost length + 3)
  calc
    runTime requests [] ≤ 3 + requests.length * unitCost length := raw
    _ ≤ 3 + length * unitCost length :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _
    _ ≤ (length + 1) * (unitCost length + 3) := by
      nlinarith [Nat.zero_le length, Nat.zero_le (unitCost length)]

end GadgetSparseRouteRecordBatch
end
end LeanTrominoes
