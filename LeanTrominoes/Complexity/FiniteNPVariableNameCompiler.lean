/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteNPCompilerPreparation
import LeanTrominoes.Complexity.FiniteNPCompilerRequest
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnPairCompiler

/-! # Native polynomial-time absolute variable-name generation

The prepared unary slice and atom bounds drive a Cartesian enumeration of
all absolute variable names. The request's fresh-atom header is also computed
by a fixed polynomial-time machine from the original source word.
-/
noncomputable section
namespace LeanTrominoes.FiniteNPVariableNameCompiler
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
open FiniteNPCompilerPreparation
open Complexity.VerifierInPolyTime
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)

abbrev Source := Symbol encoding.Γ

def nameRows (word : List (Source (encoding := encoding))) : List (Nat × Nat) :=
  (List.range (counterCount 1 word+1)).flatMap fun time =>
    (List.range (counterCount 3 word)).map fun atom => (time,atom)

def names (word : List (Source (encoding := encoding))) : List Nat :=
  (nameRows word).map (fun row => Nat.pair row.1 row.2)

/-- An extra time slice includes next wires in the last emitted expression. -/
def slicesCompiler : ScalarCompiler (fun word : List (Source (encoding := encoding)) => counterCount 1 word+1) := by
  let slices := counterComputableInPolyTime (Source := encoding.Γ) 1
  let column : Compiler (fun _ : List (Source (encoding := encoding)) => [()])
      (fun word _ => counterCount 1 word) := slices
  exact add column (constant column 1)

def computableInPolyTime : TM2ComputableInPolyTime id unaryFields (names (encoding := encoding)) := by
  let times := naturalRange (slicesCompiler (encoding := encoding))
  let atoms := naturalRange (counterComputableInPolyTime (Source := encoding.Γ) 3)
  exact pair (cartesianLeft times atoms) (cartesianRight times atoms)

/-- Direct source words generate the complete variable-name table. -/
def sourceNames (symbols : List encoding.Γ) : List Nat := names (prepared verifier symbols)

def sourceComputableInPolyTime : TM2ComputableInPolyTime id unaryFields (sourceNames verifier) := by
  unfold sourceNames
  exact TM2CompositionMachine.computableInPolyTime (FiniteNPCompilerPreparation.computableInPolyTime verifier)
    (computableInPolyTime (encoding := encoding))

theorem sourceNames_eq (symbols : List encoding.Γ) : sourceNames verifier symbols=
    ((List.range ((timePolynomial verifier).eval symbols.length+2)).flatMap fun time =>
      (List.range ((tableauSourcePolynomial verifier+tableauGatePolynomial verifier).eval symbols.length)).map
        fun atom => (time,atom)).map (fun row => Nat.pair row.1 row.2) := by
  simp [sourceNames,names,nameRows,counterCount_prepared,Nat.add_assoc]

def freshUnits {Source : Type} : Symbol Source → List Unit
  | .inl _ => []
  | .inr _ => [()]

def sourceFresh (symbols : List encoding.Γ) : Nat := (requestFreshPolynomial verifier).eval symbols.length

/-- Computing a large numeric header uses unary polynomial padding, rather
than assuming a polynomial output-size bound implies a time bound. -/
def freshComputableInPolyTime : TM2ComputableInPolyTime id unaryFields
    (fun symbols => [sourceFresh verifier symbols]) := by
  let embedded := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : encoding.Γ => [(Sum.inl symbol : Symbol encoding.Γ)])
  let padded := TM2CompositionMachine.computableInPolyTime embedded
    (addCounterComputableInPolyTime 0 (requestFreshPolynomial verifier))
  let counted := TM2CompositionMachine.computableInPolyTime padded
    (counterComputableInPolyTime (Source := encoding.Γ) 0)
  apply TM2ComputableInPolyTime.of_eq counted
  intro symbols
  simp only [← List.map_eq_flatMap]
  simp [sourceFresh,addCounter]

end LeanTrominoes.FiniteNPVariableNameCompiler
