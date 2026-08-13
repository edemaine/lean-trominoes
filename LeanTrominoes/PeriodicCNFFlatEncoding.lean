import LeanTrominoes.PeriodicCNF
import Mathlib.Computability.Encoding

/-!
# A flat finite encoding of periodic CNF formulas

The standard `Primcodable` instance for `PeriodicCNF` recursively Cantor-pairs
list heads with list tails.  Its binary representation is therefore not an
appropriate output format for polynomial-time reductions: even a short list
of small entries can acquire exponentially many bits.

This file gives periodic CNF formulas a flat, self-delimiting representation.
The alphabet consists of binary digits and one field delimiter.  The natural
number fields begin with the number of clauses; each clause then begins with
its number of literals; and every literal occupies four fields (atom, two
signed coordinates, and Boolean value).  Thus list structure contributes only
linearly many symbols.
-/

namespace LeanTrominoes

open Computability

namespace PeriodicCNFFlatEncoding

/-- A binary digit, or the delimiter terminating one natural-number field. -/
abbrev Symbol := Option Bool

/-- Encode a list of naturals as delimiter-terminated little-endian binary
fields.  In particular, zero is represented by a delimiter with no preceding
digits. -/
def encodeNatFields (fields : List Nat) : List Symbol :=
  fields.flatMap fun field => (encodeNat field).map some ++ [none]

/-- Decode delimiter-terminated binary fields.  `reversedBits` is the portion
of the current field already consumed, in reverse order. -/
def decodeNatFieldsAux : List Bool → List Symbol → Option (List Nat)
  | [], [] => some []
  | _ :: _, [] => none
  | reversedBits, some bit :: symbols =>
      decodeNatFieldsAux (bit :: reversedBits) symbols
  | reversedBits, none :: symbols =>
      (decodeNat reversedBits.reverse :: ·) <$> decodeNatFieldsAux [] symbols

/-- Decode a complete stream of natural-number fields. -/
def decodeNatFields (symbols : List Symbol) : Option (List Nat) :=
  decodeNatFieldsAux [] symbols

theorem decodeNatFieldsAux_bits (reversedBits bits : List Bool)
    (symbols : List Symbol) :
    decodeNatFieldsAux reversedBits (bits.map some ++ symbols) =
      decodeNatFieldsAux (bits.reverse ++ reversedBits) symbols := by
  induction bits generalizing reversedBits with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.map_cons, List.cons_append, decodeNatFieldsAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem decodeNatFields_encodeNatFields (fields : List Nat) :
    decodeNatFields (encodeNatFields fields) = some fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      have ih' : decodeNatFieldsAux [] (encodeNatFields fields) =
          some fields := ih
      rw [show encodeNatFields (field :: fields) =
          (encodeNat field).map some ++ none :: encodeNatFields fields by
        simp [encodeNatFields]]
      unfold decodeNatFields
      rw [decodeNatFieldsAux_bits]
      simp [decodeNatFieldsAux, ih']

@[simp]
theorem encodeNatFields_length (fields : List Nat) :
    (encodeNatFields fields).length =
      (fields.map fun field => (encodeNat field).length + 1).sum := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp [encodeNatFields]
      omega

/-- Decode one signed coordinate field.  Values outside the range of the
standard integer code are harmlessly sent to zero; encoded coordinates round
trip exactly. -/
def decodeIntField (field : Nat) : Int :=
  (Encodable.decode field : Option Int).getD 0

@[simp]
theorem decodeIntField_encode (coordinate : Int) :
    decodeIntField (Encodable.encode coordinate) = coordinate := by
  unfold decodeIntField
  rw [Encodable.encodek]
  rfl

/-- Encode a Boolean as one natural-number field. -/
def encodeBoolField (value : Bool) : Nat :=
  if value then 1 else 0

/-- Decode a Boolean field.  The generated representation uses only zero and
one, while accepting every nonzero field as true keeps the decoder total. -/
def decodeBoolField (field : Nat) : Bool :=
  field != 0

@[simp]
theorem decodeBoolField_encode (value : Bool) :
    decodeBoolField (encodeBoolField value) = value := by
  cases value <;> rfl

/-- The four flat natural-number fields of one literal. -/
def literalFields (literal : PeriodicLiteral Nat) : List Nat :=
  [literal.atom,
    Encodable.encode literal.offset.1,
    Encodable.encode literal.offset.2,
    encodeBoolField literal.value]

/-- Parse one literal, leaving the unconsumed fields. -/
def decodeLiteralFields : List Nat →
    Option (PeriodicLiteral Nat × List Nat)
  | atom :: x :: y :: value :: rest =>
      some (⟨atom, (decodeIntField x, decodeIntField y),
        decodeBoolField value⟩, rest)
  | _ => none

@[simp]
theorem decodeLiteralFields_literalFields_append
    (literal : PeriodicLiteral Nat) (rest : List Nat) :
    decodeLiteralFields (literalFields literal ++ rest) =
      some (literal, rest) := by
  rcases literal with ⟨atom, ⟨x, y⟩, value⟩
  simp [literalFields, decodeLiteralFields]

/-- Parse exactly `count` literals, leaving the unconsumed fields. -/
def decodeLiterals : Nat → List Nat →
    Option (List (PeriodicLiteral Nat) × List Nat)
  | 0, fields => some ([], fields)
  | count + 1, fields => do
      let (literal, rest) ← decodeLiteralFields fields
      let (literals, suffix) ← decodeLiterals count rest
      pure (literal :: literals, suffix)

@[simp]
theorem decodeLiterals_flatMap_literalFields_append
    (literals : List (PeriodicLiteral Nat)) (rest : List Nat) :
    decodeLiterals literals.length
        (literals.flatMap literalFields ++ rest) =
      some (literals, rest) := by
  induction literals with
  | nil => simp [decodeLiterals]
  | cons literal literals ih =>
      simp [decodeLiterals, ih]

/-- Flat fields for one clause: its literal count followed by its literals. -/
def clauseFields (clause : PeriodicClause Nat) : List Nat :=
  clause.length :: clause.flatMap literalFields

/-- Parse exactly `count` clauses, leaving the unconsumed fields. -/
def decodeClauses : Nat → List Nat →
    Option (List (PeriodicClause Nat) × List Nat)
  | 0, fields => some ([], fields)
  | count + 1, literalCount :: fields => do
      let (clause, rest) ← decodeLiterals literalCount fields
      let (clauses, suffix) ← decodeClauses count rest
      pure (clause :: clauses, suffix)
  | _ + 1, [] => none

@[simp]
theorem decodeClauses_flatMap_clauseFields_append
    (clauses : List (PeriodicClause Nat)) (rest : List Nat) :
    decodeClauses clauses.length (clauses.flatMap clauseFields ++ rest) =
      some (clauses, rest) := by
  induction clauses with
  | nil => simp [decodeClauses]
  | cons clause clauses ih =>
      simp [clauseFields, decodeClauses, ih]

/-- Flat natural-number fields for a complete periodic CNF formula. -/
def formulaFields (formula : PeriodicCNF Nat) : List Nat :=
  formula.clauses.length :: formula.clauses.flatMap clauseFields

/-- Decode a complete flat field list, rejecting any unconsumed suffix. -/
def decodeFormulaFields : List Nat → Option (PeriodicCNF Nat)
  | clauseCount :: fields => do
      let (clauses, rest) ← decodeClauses clauseCount fields
      if rest.isEmpty then some ⟨clauses⟩ else none
  | [] => none

@[simp]
theorem decodeFormulaFields_formulaFields (formula : PeriodicCNF Nat) :
    decodeFormulaFields (formulaFields formula) = some formula := by
  rcases formula with ⟨clauses⟩
  have parsed :
      decodeClauses clauses.length (clauses.flatMap clauseFields) =
        some (clauses, []) := by
    simpa using decodeClauses_flatMap_clauseFields_append clauses []
  simp [formulaFields, decodeFormulaFields, parsed]

/-- A flat finite encoding for natural-variable periodic CNF formulas. -/
def finEncoding : FinEncoding (PeriodicCNF Nat) where
  Γ := Symbol
  encode formula := encodeNatFields (formulaFields formula)
  decode symbols := (decodeNatFields symbols).bind decodeFormulaFields
  decode_encode formula := by simp
  ΓFin := inferInstance

@[simp]
theorem finEncoding_encode_length (formula : PeriodicCNF Nat) :
    (finEncoding.encode formula).length =
      ((formulaFields formula).map fun field =>
        (encodeNat field).length + 1).sum := by
  exact encodeNatFields_length _

end PeriodicCNFFlatEncoding

end LeanTrominoes
