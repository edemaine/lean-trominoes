/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteRetainedTrominoRegion
import LeanTrominoes.FiniteCNFStripSourceOffsets
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.FiniteNPProgramSource

/-! # A finite region endpoint for the shared program-source interface -/
noncomputable section
namespace LeanTrominoes.FiniteProgramTrominoRegion
open PeriodicCNF PeriodicCNFStripReduction
attribute [local instance] variableDecidableEq variableBEq
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (source : ProgramSource encoding language)
    (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

def guardedZero (symbols : List encoding.Γ) : FiniteCNF.ZeroOffsets
    (sourceFormula (source.formulaOfSymbols symbols)) :=
  sourceFormula_zeroOffsets _ (formulaOfSymbols_widthAtMostThree source symbols) (zero symbols)

def regionOfSymbols (t : Tromino) (symbols : List encoding.Γ) : List Cell :=
  let raw := source.formulaOfSymbols symbols
  FiniteRetainedTrominoRegion.region (sourceFormula raw) (sourceFormula_isLocal raw)
    (sourceFormula_widthAtMostThree raw) (sourceFormula_occurrencesAtMostThree_canonicalBEq raw)
    (sourceFormula_clausesNonempty raw) (guardedZero source zero symbols) t

def region (t : Tromino) (input : Input) : List Cell :=
  regionOfSymbols source zero t (encoding.encode input)

theorem correct (t : Tromino) (input : Input) :
    language input ↔ t.Tileable ((region source zero t input).toFinset : Set Cell) := by
  let raw := source.formulaOfSymbols (encoding.encode input)
  have core := FiniteRetainedTrominoRegion.correct (sourceFormula raw) (sourceFormula_isLocal raw)
    (sourceFormula_widthAtMostThree raw) (sourceFormula_occurrencesAtMostThree_canonicalBEq raw)
    (sourceFormula_clausesNonempty raw) (guardedZero source zero (encoding.encode input)) t
  have semantic : language input ↔ FiniteCNF.Satisfiable (FiniteCNF.erase (sourceFormula raw)) :=
    (source.correct input).trans ((sourceFormula_correct raw).trans
      (FiniteCNF.satisfiable_erase _ (guardedZero source zero (encoding.encode input))).symm)
  exact semantic.trans core

/-- Every NP verifier already has a concrete finite-region reduction function;
its polynomial-time serialization is supplied separately. -/
def npRegion (verifier : Complexity.VerifierInPolyTime encoding language) (t : Tromino) : Input → List Cell :=
  region (FiniteNPProgramSource.source verifier) (FiniteNPProgramSource.formula_zero verifier) t

theorem npRegion_correct (verifier : Complexity.VerifierInPolyTime encoding language)
    (t : Tromino) (input : Input) :
    language input ↔ t.Tileable ((npRegion verifier t input).toFinset : Set Cell) :=
  correct (FiniteNPProgramSource.source verifier) (FiniteNPProgramSource.formula_zero verifier) t input
end LeanTrominoes.FiniteProgramTrominoRegion
