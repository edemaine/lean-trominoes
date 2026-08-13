import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PartrecPolySpace

/-!
# Native natural fields for arbitrary finite alphabets

Every source encoding quantified over by `PSPACEHard` may use a different
finite alphabet.  The partial-recursive evaluator, by contrast, expects its
input as delimiter-terminated binary naturals over `PartrecToTM2.Γ'`.

This file numbers an arbitrary finite alphabet, emits the canonical native
field for each symbol, and specializes `FiniteBlockTransducer` to prove that
the conversion is polynomial-time.  Because every source-symbol block has
constant length, the certificate is linear in the source encoding length.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace FiniteEncodingNativeFields

/-- The fixed natural index of a symbol in an arbitrary finite alphabet. -/
def symbolIndex {Symbol : Type} [Fintype Symbol] (symbol : Symbol) : Nat :=
  (Fintype.equivFin Symbol symbol).val

/-- The natural field list represented by a source-symbol stream. -/
def fields {Symbol : Type} [Fintype Symbol]
    (symbols : List Symbol) : List Nat :=
  symbols.map symbolIndex

/-- Canonical evaluator-alphabet block for one source symbol. -/
def symbolBlock {Symbol : Type} [Fintype Symbol]
    (symbol : Symbol) : List PartrecToTM2.Γ' :=
  PartrecToTM2.trNat (symbolIndex symbol) ++ [.cons]

/-- Direct native encoding of a source-symbol stream as natural fields. -/
def encode {Symbol : Type} [Fintype Symbol]
    (symbols : List Symbol) : List PartrecToTM2.Γ' :=
  PartrecToTM2.trList (fields symbols)

theorem flatMap_symbolBlock_eq_encode
    {Symbol : Type} [Fintype Symbol] (symbols : List Symbol) :
    symbols.flatMap symbolBlock = encode symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [symbolBlock, encode, fields, PartrecToTM2.trList, induction]

@[simp]
theorem encode_length {Symbol : Type} [Fintype Symbol]
    (symbols : List Symbol) :
    (encode symbols).length =
      (symbols.map fun symbol =>
        (encodeNat (symbolIndex symbol)).length + 1).sum := by
  change PartrecToTM2.encodedListSpace (fields symbols) = _
  rw [PartrecToTM2.encodedListSpace_eq_sum]
  unfold fields
  rw [List.map_map]
  change (symbols.map fun symbol =>
    (encodeNat (symbolIndex symbol)).length + 1).sum = _
  rfl

/-- The generic block transducer specialized to canonical native natural
fields for one finite source alphabet. -/
def computableInPolyTime {Symbol : Type}
    [Fintype Symbol] :
    @TM2ComputableInPolyTime
      (List Symbol) (List PartrecToTM2.Γ')
      Symbol PartrecToTM2.Γ' id id encode := by
  let certificate :=
    FiniteBlockTransducer.computableInPolyTime
      (Source := Symbol) (Target := PartrecToTM2.Γ')
      (symbolBlock (Symbol := Symbol))
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro symbols
  simpa only [flatMap_symbolBlock_eq_encode] using
    certificate.outputsFun symbols

/-- The same physical transducer, presented with its semantic output as the
list of natural fields rather than as the already-encoded native symbol
stream.  This is the interface needed for composition with an evaluator whose
input encoding is `PartrecToTM2.trList`. -/
def fieldsComputableInPolyTime {Symbol : Type}
    [Fintype Symbol] :
    @TM2ComputableInPolyTime
      (List Symbol) (List Nat)
      Symbol PartrecToTM2.Γ' id PartrecToTM2.trList fields := by
  let certificate := computableInPolyTime (Symbol := Symbol)
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro symbols
  simpa only [encode, id_eq] using certificate.outputsFun symbols

@[simp]
theorem fields_length {Symbol : Type} [Fintype Symbol]
    (symbols : List Symbol) :
    (fields symbols).length = symbols.length := by
  simp [fields]

/-- Every natural field contributes at least its terminating delimiter. -/
theorem fields_length_le_encode_length
    {Symbol : Type} [Fintype Symbol] (symbols : List Symbol) :
    (fields symbols).length ≤ (encode symbols).length := by
  rw [encode_length, fields_length]
  induction symbols with
  | nil => simp
  | cons symbol symbols induction =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- The preprocessing time polynomial is explicitly linear. -/
theorem time_eq_linear {Symbol : Type} [Fintype Symbol] :
    (computableInPolyTime (Symbol := Symbol)).time =
      FiniteBlockTransducer.timePolynomial
        (symbolBlock (Symbol := Symbol)) := by
  rfl

end FiniteEncodingNativeFields

end LeanTrominoes
