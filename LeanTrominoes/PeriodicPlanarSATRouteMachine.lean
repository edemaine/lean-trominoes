/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteProgram

/-! # The compiled route query on native formula-and-drawing inputs

This module certifies execution and space. The identification of its result
with graph route matching is a separate semantic obligation.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open FlatEncoding BoundedArithmetic
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def result (input : Input Nat) : Bool := decide (program.value (RouteInput.context input) ≠ 0)
def code : Code := (NativeScalar.normalize program).code.comp RouteInput.code

def coefficient : Nat := (NativeScalar.normalize program).coefficient*(RouteInput.coefficient+1)+RouteInput.coefficient

theorem code_eval (input : Input Nat) : code.eval (fields input) = pure [(result input).toNat] := by
  simp [code,RouteInput.code_eval,(NativeScalar.normalize program).evaluates,
    NativeScalar.normalize_value,result,Part.bind_eq_bind]

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits code (fields input) [(result input).toNat]
      (coefficient*((finEncoding.encode input).length+1)) := by
  have guard := (NativeScalar.normalize program).fits (RouteInput.context input)
  rw [NativeScalar.normalize_value] at guard
  have prepare := RouteInput.code_fits input
  rw [← fields_space] at prepare
  have fit := comp_linear guard prepare
  rw [fields_space] at fit
  exact fit

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
