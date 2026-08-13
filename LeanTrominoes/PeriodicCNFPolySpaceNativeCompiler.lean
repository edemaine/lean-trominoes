import LeanTrominoes.PeriodicCNFPolySpaceCompiler
import LeanTrominoes.FiniteEncodingNativeFields
import LeanTrominoes.TM2CompositionMachine

/-!
# Native-field interface to the periodic-CNF hardness compiler

The source-alphabet front end emits one bounded natural field per source
symbol.  This file gives the semantic formula compiler exactly that field-list
interface.  On fields produced by the front end it recovers the original
symbol stream, then exposes the flat CNF natural fields whose native
`PartrecToTM2.trList` encoding is the already-verified flat formula encoding.

This isolates the remaining machine task precisely: prove
`nativeCompilerFields` polynomial-time between two native `trList` encodings.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceNativeCompiler

/-- Decode one bounded index in an arbitrary finite alphabet.  Invalid fields
are rejected; generated source fields are always valid. -/
def decodeSymbolField (Symbol : Type) [Fintype Symbol]
    (field : Nat) : Option Symbol :=
  if bound : field < Fintype.card Symbol then
    some ((Fintype.equivFin Symbol).symm ⟨field, bound⟩)
  else
    none

@[simp]
theorem decodeSymbolField_symbolIndex
    {Symbol : Type} [Fintype Symbol] (symbol : Symbol) :
    decodeSymbolField Symbol
      (FiniteEncodingNativeFields.symbolIndex symbol) = some symbol := by
  simp [decodeSymbolField, FiniteEncodingNativeFields.symbolIndex]

/-- Decode a list of source-symbol fields.  The empty-list fallback makes the
function total on malformed field streams; it is unreachable after the
verified front end. -/
def symbolsOfFields (Symbol : Type) [Fintype Symbol] :
    List Nat → List Symbol
  | [] => []
  | field :: fields =>
      match decodeSymbolField Symbol field with
      | some symbol => symbol :: symbolsOfFields Symbol fields
      | none => []

@[simp]
theorem symbolsOfFields_fields
    {Symbol : Type} [Fintype Symbol] (symbols : List Symbol) :
    symbolsOfFields Symbol
      (FiniteEncodingNativeFields.fields symbols) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      rw [show FiniteEncodingNativeFields.fields (symbol :: symbols) =
        FiniteEncodingNativeFields.symbolIndex symbol ::
          FiniteEncodingNativeFields.fields symbols by rfl]
      simp [symbolsOfFields, induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Flat CNF natural fields computed from evaluator-native source fields. -/
def nativeCompilerFields (fields : List Nat) : List Nat :=
  PeriodicCNFFlatEncoding.formulaFields
    (PolySpaceCompiler.formulaOfSymbols decider
      (symbolsOfFields encoding.Γ fields))

@[simp]
theorem nativeCompilerFields_sourceFields (symbols : List encoding.Γ) :
    nativeCompilerFields decider
        (FiniteEncodingNativeFields.fields symbols) =
      PeriodicCNFFlatEncoding.formulaFields
        (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  simp [nativeCompilerFields]

@[simp]
theorem nativeCompilerFields_encode (input : Input) :
    nativeCompilerFields decider
        (FiniteEncodingNativeFields.fields (encoding.encode input)) =
      PeriodicCNFFlatEncoding.formulaFields
        (PolySpaceReduction.formula decider input) := by
  simp [nativeCompilerFields]

/-- On generated source fields, encoding the compiler's natural-field output
is definitionally the verified flat formula symbol stream. -/
theorem trList_nativeCompilerFields_sourceFields
    (symbols : List encoding.Γ) :
    PartrecToTM2.trList
        (nativeCompilerFields decider
          (FiniteEncodingNativeFields.fields symbols)) =
      PolySpaceCompiler.compiler decider symbols := by
  rw [nativeCompilerFields_sourceFields]
  unfold PolySpaceCompiler.compiler PeriodicCNFFlatEncoding.finEncoding
    PeriodicCNFFlatEncoding.finEncodingOfFields
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _ |>.symm

theorem trList_nativeCompilerFields_encode (input : Input) :
    PartrecToTM2.trList
        (nativeCompilerFields decider
          (FiniteEncodingNativeFields.fields (encoding.encode input))) =
      PeriodicCNFFlatEncoding.finEncoding.encode
        (PolySpaceReduction.formula decider input) := by
  rw [nativeCompilerFields_encode]
  unfold PeriodicCNFFlatEncoding.finEncoding
    PeriodicCNFFlatEncoding.finEncodingOfFields
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _ |>.symm

/-- The native output stream retains the already-proved polynomial length
bound, now measured against the (at least as long) native source stream. -/
theorem native_output_length_le_polynomial_eval (input : Input) :
    (PartrecToTM2.trList
      (nativeCompilerFields decider
        (FiniteEncodingNativeFields.fields (encoding.encode input)))).length ≤
      (PolySpaceReduction.formulaEncodingPolynomial decider).eval
        (FiniteEncodingNativeFields.encode
          (encoding.encode input)).length := by
  rw [trList_nativeCompilerFields_encode]
  apply (PolySpaceReduction.formula_encoding_length_le_polynomial_eval
    decider input).trans
  exact TM2CompositionMachine.polynomial_eval_monotone
    (PolySpaceReduction.formulaEncodingPolynomial decider)
    (FiniteEncodingNativeFields.fields_length_le_encode_length
      (encoding.encode input))

end PolySpaceNativeCompiler
end PeriodicCNF
end LeanTrominoes
