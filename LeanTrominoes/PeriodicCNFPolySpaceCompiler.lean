import LeanTrominoes.PeriodicCNFPolySpaceReductionSize

/-!
# Encoded-input compiler for the local periodic-CNF reduction

The semantic reduction is stated on values of the source type, but its output
depends on such a value only through its finite encoding.  This file factors
that dependence through a concrete function on source symbol lists and makes
the flat CNF symbol stream its direct output.  The resulting `compiler` is the
function for which the subsequent Turing-machine time certificate is needed.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PolySpaceCompiler

variable {Input : Type} {encoding : Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Initial machine configuration constructed directly from an encoded source
symbol list. -/
def initialConfigurationOfSymbols
    (symbols : List encoding.Γ) : decider.tm.Cfg :=
  initList decider.tm (List.map decider.inputAlphabet.invFun symbols)

/-- The same explicit width budget as the semantic reduction, expressed only
in terms of the raw source symbols. -/
def spaceOfSymbols (symbols : List encoding.Γ) : Nat :=
  decider.space.eval symbols.length + symbols.length +
    Complexity.configurationSpace decider.tm
      (PolySpaceReduction.acceptingConfiguration decider)

/-- Reset-clock width computed directly from raw source symbols. -/
def clockBitsOfSymbols (symbols : List encoding.Γ) : Nat :=
  BoundedMachineAtom.configurationBitCount (tm := decider.tm)
    (space := spaceOfSymbols decider symbols)

/-- Periodic CNF compiled directly from the raw source symbol list. -/
def formulaOfSymbols (symbols : List encoding.Γ) : PeriodicCNF Nat :=
  BoundedMachineAtom.designatedMachinePeriodicCNF
    (tm := decider.tm) (space := spaceOfSymbols decider symbols)
    (clockBits := clockBitsOfSymbols decider symbols)
    (initialConfigurationOfSymbols decider symbols)
    (PolySpaceReduction.acceptingConfiguration decider)

/-- Direct flat output symbol stream of the hardness compiler. -/
def compiler (symbols : List encoding.Γ) :
    List PeriodicCNFFlatEncoding.Symbol :=
  PeriodicCNFFlatEncoding.finEncoding.encode
    (formulaOfSymbols decider symbols)

@[simp]
theorem initialConfigurationOfSymbols_encode (input : Input) :
    initialConfigurationOfSymbols decider (encoding.encode input) =
      PolySpaceReduction.initialConfiguration decider input := by
  rfl

@[simp]
theorem spaceOfSymbols_encode (input : Input) :
    spaceOfSymbols decider (encoding.encode input) =
      PolySpaceReduction.reductionSpace decider input := by
  unfold spaceOfSymbols PolySpaceReduction.reductionSpace
  rw [show Complexity.configurationSpace decider.tm
      (PolySpaceReduction.initialConfiguration decider input) =
        (encoding.encode input).length by
    unfold PolySpaceReduction.initialConfiguration
    rw [PolySpaceReduction.configurationSpace_initList]
    simp]

@[simp]
theorem clockBitsOfSymbols_encode (input : Input) :
    clockBitsOfSymbols decider (encoding.encode input) =
      PolySpaceReduction.reductionClockBits decider input := by
  simp [clockBitsOfSymbols, PolySpaceReduction.reductionClockBits]

@[simp]
theorem formulaOfSymbols_encode (input : Input) :
    formulaOfSymbols decider (encoding.encode input) =
      PolySpaceReduction.formula decider input := by
  simp [formulaOfSymbols, PolySpaceReduction.formula]

@[simp]
theorem compiler_encode (input : Input) :
    compiler decider (encoding.encode input) =
      PeriodicCNFFlatEncoding.finEncoding.encode
        (PolySpaceReduction.formula decider input) := by
  simp [compiler]

/-- Semantic correctness at the encoded-list compiler interface. -/
theorem mem_iff_compiler_formula_satisfiable (input : Input) :
    language input ↔
      LocalPeriodicCNF1DSAT (formulaOfSymbols decider
        (encoding.encode input)) := by
  rw [formulaOfSymbols_encode]
  exact PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

/-- The compiler output itself obeys the polynomial symbol bound already
proved for the semantic reduction. -/
theorem compiler_length_le_polynomial_eval (input : Input) :
    (compiler decider (encoding.encode input)).length ≤
      (PolySpaceReduction.formulaEncodingPolynomial decider).eval
        (encoding.encode input).length := by
  rw [compiler_encode]
  exact PolySpaceReduction.formula_encoding_length_le_polynomial_eval
    decider input

end PolySpaceCompiler

end PeriodicCNF

end LeanTrominoes
