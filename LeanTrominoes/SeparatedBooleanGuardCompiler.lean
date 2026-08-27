/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Guarding a separated word by one Boolean -/

noncomputable section

namespace LeanTrominoes.SeparatedBooleanGuard

open Computability Turing

inductive Control
  | guard (active : Bool)
  | body (active : Bool)
  deriving DecidableEq, Fintype

def transition {Symbol : Type} :
    Control → SeparatedProductEncoding.Token Bool Symbol →
      Control × List Symbol
  | .guard _, .left active => (.guard active, [])
  | .guard active, .separator => (.body active, [])
  | .guard active, .right _ => (.guard active, [])
  | .body active, .right symbol =>
      (.body active, if active then [symbol] else [])
  | .body active, .left _ => (.body active, [])
  | .body active, .separator => (.body active, [])

def finish {Symbol : Type} (_ : Control) : List Symbol := []

/-- Retain the word exactly when its separated Boolean guard is true. -/
def guarded {Symbol : Type} (pair : Bool × List Symbol) : List Symbol :=
  if pair.1 then pair.2 else []

theorem scan_right {Symbol : Type} (active : Bool) (word : List Symbol) :
    FiniteStateTransducer.scan transition (.body active)
        (word.map SeparatedProductEncoding.Token.right) =
      (.body active, if active then word else []) := by
  induction word with
  | nil => cases active <;> rfl
  | cons symbol word induction =>
      cases active <;>
        simp [FiniteStateTransducer.scan, transition, induction]

@[simp] theorem output_encode {Symbol : Type}
    (active : Bool) (word : List Symbol) :
    FiniteStateTransducer.output (.guard false) transition finish
        (SeparatedProductEncoding.encode (fun bit => [bit]) id
          (active, word)) =
      guarded (active, word) := by
  have scanEq :
      FiniteStateTransducer.scan transition (.guard false)
          (SeparatedProductEncoding.encode (fun bit => [bit]) id
            (active, word)) =
        (.body active, if active then word else []) := by
    change FiniteStateTransducer.scan transition (.guard false)
        (SeparatedProductEncoding.Token.left active ::
          SeparatedProductEncoding.Token.separator ::
            word.map SeparatedProductEncoding.Token.right) = _
    simp only [FiniteStateTransducer.scan, transition]
    exact scan_right active word
  unfold FiniteStateTransducer.output
  rw [scanEq]
  cases active <;> simp [finish, guarded]

/-- A singleton Boolean prefix can guard an arbitrary finite-alphabet word
by a fixed finite-state transducer. -/
noncomputable def computableInPolyTime
    {Symbol : Type} [Fintype Symbol] [Inhabited Symbol] :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode (fun bit => [bit]) id)
      id (guarded (Symbol := Symbol)) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode (fun bit => [bit]) id)
    (FiniteStateTransducer.computableInPolyTime
      (Control.guard false) transition finish)
    (fun _ => rfl)
    (fun pair => by
      rcases pair with ⟨active, word⟩
      exact output_encode active word)

end LeanTrominoes.SeparatedBooleanGuard

end
