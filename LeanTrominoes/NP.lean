/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityReductions

/-! # NP via polynomially bounded witnesses and finite-alphabet verifiers

The verifier is an actual polynomial-time multi-stack Turing machine. Its
input contains the original finite-alphabet input, a separator, and a binary
certificate. Merely having a finite or short certificate does not establish
membership: the polynomial-time verifier is a required field.
-/
namespace LeanTrominoes.Complexity
open Computability

/-- Disjoint tags prevent input symbols from being confused with certificate
bits or with the separator. -/
def encodeWitness {α : Type} (encoding : FinEncoding α) (input : α × List Bool) :
    List (Sum encoding.Γ (Option Bool)) :=
  (encoding.encode input.1).map Sum.inl ++
    Sum.inr none :: input.2.map (fun bit => Sum.inr (some bit))

theorem encodeWitness_length {α : Type} (encoding : FinEncoding α) (input : α × List Bool) :
    (encodeWitness encoding input).length=(encoding.encode input.1).length+input.2.length+1 := by
  simp [encodeWitness]; omega

structure VerifierInPolyTime {α : Type} (encoding : FinEncoding α) (language : α → Prop) where
  verify : α → List Bool → Bool
  computer : FiniteAlphabetComputableInPolyTime (encodeWitness encoding)
    (primcodableFinEncoding Bool).encode (fun input => verify input.1 input.2)
  witnessBound : Polynomial Nat
  correct : ∀ input, language input ↔ ∃ witness : List Bool,
    witness.length≤witnessBound.eval (encoding.encode input).length ∧ verify input witness=true

def InNP {α : Type} (encoding : FinEncoding α) (language : α → Prop) : Prop :=
  Nonempty (VerifierInPolyTime encoding language)

def NPHard {β : Type} (encoding : FinEncoding β) (language : β → Prop) : Prop :=
  ∀ {α : Type} (sourceEncoding : FinEncoding α) (source : α → Prop),
    InNP sourceEncoding source → PolyTimeManyOneReducible sourceEncoding encoding source language

def NPComplete {α : Type} (encoding : FinEncoding α) (language : α → Prop) : Prop :=
  InNP encoding language ∧ NPHard encoding language

theorem NPHard.of_reduction {α β : Type} {sourceEncoding : FinEncoding α}
    {targetEncoding : FinEncoding β} {source : α → Prop} {target : β → Prop}
    (hard : NPHard sourceEncoding source)
    (reduction : PolyTimeManyOneReducible sourceEncoding targetEncoding source target) :
    NPHard targetEncoding target := by
  intro γ encoding language member
  exact (hard encoding language member).trans reduction

end LeanTrominoes.Complexity
