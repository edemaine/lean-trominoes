import LeanTrominoes.PeriodicCNFPolySpaceCompiler
import LeanTrominoes.PeriodicCNFTransitionExprFields
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

/-- The field-level and finite-encoding views of a flat formula agree without
unfolding the formula that produced those fields. -/
theorem trList_formulaFields_eq_finEncoding_encode
    (formula : PeriodicCNF Nat) :
    PartrecToTM2.trList
        (PeriodicCNFFlatEncoding.formulaFields formula) =
      PeriodicCNFFlatEncoding.finEncoding.encode formula := by
  change PartrecToTM2.trList
      (PeriodicCNFFlatEncoding.formulaFields formula) =
    PeriodicCNFFlatEncoding.encodeNatFields
      (PeriodicCNFFlatEncoding.formulaFields formula)
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _ |>.symm

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

/-- The bounded transition expression constructed from evaluator-native source
fields.  The decider contributes only fixed finite data; all runtime widths are
computed from the decoded source-symbol stream. -/
def nativeCompilerExpression (fields : List Nat) : TransitionExpr :=
  let symbols := symbolsOfFields encoding.Γ fields
  let space := PolySpaceCompiler.spaceOfSymbols decider symbols
  let clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols
  BoundedMachineAtom.designatedMachineResetClockExpression
    (tm := decider.tm) (space := space) (clockBits := clockBits)
    (PolySpaceCompiler.initialConfigurationOfSymbols decider symbols)
    (PolySpaceReduction.acceptingConfiguration decider)

/-- First fresh Tseitin atom for the native-field expression. -/
def nativeCompilerFresh (fields : List Nat) : Nat :=
  let symbols := symbolsOfFields encoding.Γ fields
  BoundedMachineAtom.atomCount (tm := decider.tm)
    (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
    (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)

/-- Flat CNF natural fields computed directly from evaluator-native source
fields.  This version streams gate fields structurally and never constructs an
intermediate list of clauses. -/
def nativeCompilerFields (fields : List Nat) : List Nat :=
  requireTransitionExprFields
    (nativeCompilerExpression decider fields)
    (nativeCompilerFresh decider fields)

/-- The direct field stream agrees exactly with the original semantic formula
construction on every input, including malformed native field lists. -/
theorem nativeCompilerFields_eq_formulaFields (fields : List Nat) :
    nativeCompilerFields decider fields =
      PeriodicCNFFlatEncoding.formulaFields
        (PolySpaceCompiler.formulaOfSymbols decider
          (symbolsOfFields encoding.Γ fields)) := by
  rw [nativeCompilerFields, requireTransitionExprFields_eq_formulaFields]
  rfl

@[simp]
theorem nativeCompilerFields_sourceFields (symbols : List encoding.Γ) :
    nativeCompilerFields decider
        (FiniteEncodingNativeFields.fields symbols) =
      PeriodicCNFFlatEncoding.formulaFields
        (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  rw [nativeCompilerFields_eq_formulaFields]
  simp

@[simp]
theorem nativeCompilerFields_encode (input : Input) :
    nativeCompilerFields decider
        (FiniteEncodingNativeFields.fields (encoding.encode input)) =
      PeriodicCNFFlatEncoding.formulaFields
        (PolySpaceReduction.formula decider input) := by
  rw [nativeCompilerFields_sourceFields,
    PolySpaceCompiler.formulaOfSymbols_encode]

/-- On generated source fields, encoding the compiler's natural-field output
is definitionally the verified flat formula symbol stream. -/
theorem trList_nativeCompilerFields_sourceFields
    (symbols : List encoding.Γ) :
    PartrecToTM2.trList
        (nativeCompilerFields decider
          (FiniteEncodingNativeFields.fields symbols)) =
      PolySpaceCompiler.compiler decider symbols := by
  rw [nativeCompilerFields_sourceFields]
  exact trList_formulaFields_eq_finEncoding_encode _

theorem trList_nativeCompilerFields_encode (input : Input) :
    PartrecToTM2.trList
        (nativeCompilerFields decider
          (FiniteEncodingNativeFields.fields (encoding.encode input))) =
      PeriodicCNFFlatEncoding.finEncoding.encode
        (PolySpaceReduction.formula decider input) := by
  rw [nativeCompilerFields_encode]
  exact trList_formulaFields_eq_finEncoding_encode _

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
  have inputLength :
      (encoding.encode input).length ≤
        (FiniteEncodingNativeFields.encode
          (encoding.encode input)).length := by
    simpa only [FiniteEncodingNativeFields.fields_length] using
      (FiniteEncodingNativeFields.fields_length_le_encode_length
        (encoding.encode input))
  exact TM2CompositionMachine.polynomial_eval_monotone
    (PolySpaceReduction.formulaEncodingPolynomial decider)
    inputLength

end PolySpaceNativeCompiler
end PeriodicCNF
end LeanTrominoes
