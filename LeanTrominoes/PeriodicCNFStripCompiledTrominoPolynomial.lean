/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCompiledTrominoSize

/-!
# Polynomial form of the concrete strip output bound
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

def sourceFormulaPresentationPolynomial : Polynomial Nat :=
  Polynomial.C 4 + Polynomial.C 16 * Polynomial.X +
    Polynomial.C 64 * Polynomial.X ^ 2

@[simp] theorem sourceFormulaPresentationPolynomial_eval (length : Nat) :
    sourceFormulaPresentationPolynomial.eval length =
      sourceFormulaPresentationBudget length := by
  simp [sourceFormulaPresentationPolynomial,
    sourceFormulaPresentationBudget, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow]

def normalizationPeriodPolynomial : Polynomial Nat :=
  Polynomial.C normalizationPeriodFactor *
    (Polynomial.C 16 *
      (Polynomial.C 2 * sourceFormulaPresentationPolynomial +
        Polynomial.C 1))

@[simp] theorem normalizationPeriodPolynomial_eval (length : Nat) :
    normalizationPeriodPolynomial.eval length =
      normalizationPeriodBudget length := by
  simp [normalizationPeriodPolynomial, normalizationPeriodBudget,
    Polynomial.eval_add, Polynomial.eval_mul]

/-- The explicit natural polynomial obtained by substituting the source
period bound into the target strip-encoding expression. -/
def compiledTrominoStripFlatEncodingPolynomial : Polynomial Nat :=
  let period := normalizationPeriodPolynomial
  let height := Polynomial.C 3 * period + Polynomial.C 1
  let motif := period * height * Polynomial.C 36
  (Polynomial.C 6 * height + Polynomial.C 6 * period + motif +
      motif * (Polynomial.C 12 * period + Polynomial.C 12 * height)) +
    (Polynomial.C 3 + Polynomial.C 2 * motif)

@[simp] theorem compiledTrominoStripFlatEncodingPolynomial_eval
    (length : Nat) :
    compiledTrominoStripFlatEncodingPolynomial.eval length =
      compiledTrominoStripFlatEncodingBudget length := by
  simp [compiledTrominoStripFlatEncodingPolynomial,
    compiledTrominoStripFlatEncodingBudget,
    PeriodicThreeDM.NormalizationCompiler.stripFlatEncodingBudget,
    Polynomial.eval_add, Polynomial.eval_mul]

theorem compiledTrominoStrip_flatEncoding_length_le_polynomial_eval
    (tromino : Tromino) (source : PeriodicCNF Nat) :
    (PeriodicStripFlatEncoding.finEncoding.encode
      (compiledTrominoStrip tromino source)).length ≤
        compiledTrominoStripFlatEncodingPolynomial.eval
          (PeriodicCNFFlatEncoding.finEncoding.encode source).length := by
  simpa using compiledTrominoStrip_flatEncoding_length_le tromino source

end PeriodicCNFStripReduction
end LeanTrominoes
