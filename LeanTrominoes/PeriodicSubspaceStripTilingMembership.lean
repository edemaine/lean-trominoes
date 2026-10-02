/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripMembership

/-! # The tiling half of Lemma 5.1 under native binary encoding -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip
open Turing Turing.ToPartrec Turing.PartrecToTM2

abbrev TilingInput := Nat × Data
def asCompletion (input : TilingInput) : Input := (input.1,input.2,[])
def TilingProblem (input : TilingInput) : Prop := Bounded input.2 input.1 ∧ Tileable input.2

theorem completable_empty (data : Data) : Completable (data,[]) ↔ Tileable data := by
  simp [Completable,IsCompletion,Tileable]

theorem asCompletion_correct (input : TilingInput) : Problem (asCompletion input) ↔ TilingProblem input := by
  simp only [Problem,TilingProblem,asCompletion,completable_empty]

namespace TilingEncoding
def fields (input : TilingInput) : List Nat := Encoding.fields (asCompletion input)
def decode (values : List Nat) : Option TilingInput := do
  let input ← Encoding.decode values
  if input.2.2=[] then some (input.1,input.2.1) else none
@[simp] theorem decode_fields (input : TilingInput) : decode (fields input)=some input := by
  rcases input with ⟨bound,data⟩
  simp [decode,fields,asCompletion]
def finEncoding : _root_.Computability.FinEncoding TilingInput :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decode decode_fields
end TilingEncoding

def TilingPolynomialBox (p : Polynomial Nat) (input : TilingInput) : Prop :=
  input.1≤p.eval (TilingEncoding.finEncoding.encode input).length
instance (p : Polynomial Nat) (input : TilingInput) : Decidable (TilingPolynomialBox p input) :=
  inferInstanceAs (Decidable (input.1≤p.eval (TilingEncoding.finEncoding.encode input).length))
abbrev PolynomialBoxTilingInput (p : Polynomial Nat) := {input : TilingInput // TilingPolynomialBox p input}

namespace PolynomialBoxTilingEncoding
def fields (p : Polynomial Nat) (input : PolynomialBoxTilingInput p) : List Nat := TilingEncoding.fields input.val
def decode (p : Polynomial Nat) (values : List Nat) : Option (PolynomialBoxTilingInput p) := do
  let input ← TilingEncoding.decode values
  if h : TilingPolynomialBox p input then some ⟨input,h⟩ else none
@[simp] theorem decode_fields (p : Polynomial Nat) (input : PolynomialBoxTilingInput p) :
    decode p (fields p input)=some input := by
  simp only [decode,fields,TilingEncoding.decode_fields]
  simp [input.property]
def finEncoding (p : Polynomial Nat) : _root_.Computability.FinEncoding (PolynomialBoxTilingInput p) :=
  PeriodicCNFFlatEncoding.finEncodingOfFields (fields p) (decode p) (decode_fields p)
end PolynomialBoxTilingEncoding

def asPolynomialCompletion (p : Polynomial Nat) (input : PolynomialBoxTilingInput p) : PolynomialBoxInput p :=
  ⟨asCompletion input.val,input.property⟩

noncomputable def tilingDecider (p : Polynomial Nat) :
    Complexity.DeciderInPolySpace (PolynomialBoxTilingEncoding.finEncoding p) (fun f => TilingProblem f.val) := by
  exact deciderInPolySpace_of_flatEvaluatorRunFits (PolynomialBoxTilingEncoding.fields p)
    (PolynomialBoxTilingEncoding.decode p) (PolynomialBoxTilingEncoding.decode_fields p)
    FieldSavitch.decideCode (fun f => FieldSavitch.result (asCompletion f.val))
    (fun f => (FieldSavitch.result_correct _).trans (asCompletion_correct f.val))
    (fun f => by
      unfold PolynomialBoxTilingEncoding.fields TilingEncoding.fields
      rw [FieldSavitch.decide_eval]
      apply Part.mem_some_iff.mpr
      cases FieldSavitch.result (asCompletion f.val) <;> rfl)
    (FieldSavitch.spacePolynomial p) (fun f => FieldSavitch.run_fits p (asPolynomialCompletion p f))

/-- The tiling half of Lemma 5.1 for arbitrary finite strip footprints. -/
theorem tiling_inPSPACE (p : Polynomial Nat) :
    Complexity.InPSPACE (PolynomialBoxTilingEncoding.finEncoding p) (fun f => TilingProblem f.val) :=
  ⟨tilingDecider p⟩

end LeanTrominoes.PeriodicSubspaceTiling.Strip
