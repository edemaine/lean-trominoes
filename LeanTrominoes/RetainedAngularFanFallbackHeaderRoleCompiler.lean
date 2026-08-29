/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryFormatter

/-! # Finite policy roles for carrier and bend fallback suffixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixHeaderRoles

open Computability Turing FiniteStateTransducer
open FallbackSuffixQueryFormatter

abbrev CarrierControl := Fin 4

def carrierInitial : CarrierControl := 0

def carrierKind (control : CarrierControl) :
    RetainedFallbackFanKind :=
  match control.val with
  | 0 => .escaped
  | 1 | 2 => .ordinary
  | _ => .escaped

def carrierNext (control : CarrierControl) : CarrierControl :=
  ⟨(control.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

def carrierTransition
    (control : CarrierControl)
    (direction : RetainedTerminalDirection) :
    CarrierControl × List HeaderRole :=
  (carrierNext control, [(carrierKind control, direction)])

def carrierFinish (_ : CarrierControl) : List HeaderRole := []

def carrierRoles (directions : List RetainedTerminalDirection) :
    List HeaderRole :=
  FiniteStateTransducer.output carrierInitial carrierTransition
    carrierFinish directions

private theorem carrierScan_length
    (control : CarrierControl)
    (directions : List RetainedTerminalDirection) :
    (scan carrierTransition control directions).2.length =
      directions.length := by
  induction directions generalizing control with
  | nil => rfl
  | cons direction directions induction =>
      change
        ([(carrierKind control, direction)] ++
          (scan carrierTransition (carrierNext control) directions).2).length =
            (direction :: directions).length
      simp only [List.singleton_append, List.length_cons]
      rw [induction]

@[simp] theorem carrierRoles_length
    (directions : List RetainedTerminalDirection) :
    (carrierRoles directions).length = directions.length := by
  unfold carrierRoles FiniteStateTransducer.output
  simp [carrierScan_length, carrierFinish]

theorem carrierRoles_four
    (first second third fourth : RetainedTerminalDirection)
    (rest : List RetainedTerminalDirection) :
    carrierRoles (first :: second :: third :: fourth :: rest) =
      [(.escaped, first), (.ordinary, second),
        (.ordinary, third), (.escaped, fourth)] ++
        carrierRoles rest := by
  unfold carrierRoles FiniteStateTransducer.output
  simp [scan, carrierTransition, carrierInitial, carrierNext,
    carrierKind, carrierFinish]

def bendRoles (directions : List RetainedTerminalDirection) :
    List HeaderRole :=
  directions.flatMap fun direction =>
    [(RetainedFallbackFanKind.ordinary, direction)]

@[simp] theorem bendRoles_length
    (directions : List RetainedTerminalDirection) :
    (bendRoles directions).length = directions.length := by
  simp [bendRoles]

theorem bendRoles_four
    (first second third fourth : RetainedTerminalDirection)
    (rest : List RetainedTerminalDirection) :
    bendRoles (first :: second :: third :: fourth :: rest) =
      [(.ordinary, first), (.ordinary, second),
        (.ordinary, third), (.ordinary, fourth)] ++
        bendRoles rest := by
  rfl

/-- Apply the canonical four-position carrier fallback policy in polynomial
time. -/
noncomputable def carrierRolesComputableInPolyTime :
    TM2ComputableInPolyTime id id carrierRoles :=
  FiniteStateTransducer.computableInPolyTime
    carrierInitial carrierTransition carrierFinish

/-- Apply the ordinary fallback policy to every bend terminal direction in
polynomial time. -/
noncomputable def bendRolesComputableInPolyTime :
    TM2ComputableInPolyTime id id bendRoles :=
  FiniteBlockTransducer.computableInPolyTime
    (fun direction : RetainedTerminalDirection =>
      [(RetainedFallbackFanKind.ordinary, direction)])

end FallbackSuffixHeaderRoles
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
