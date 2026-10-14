/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFPolySpaceRequestEmitter
import LeanTrominoes.PeriodicCNFStripDirectGridSize
import LeanTrominoes.PeriodicCNFStripGridUnitTokens

/-! # Direct unary orthocrossing-grid data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- One finite unary marker per unit of the exact orthocrossing grid scale. -/
def directGridUnitsOfSymbols (symbols : List encoding.Γ) : List Unit :=
  PeriodicCNF.StripGridUnitTokens.gridUnits
    (PeriodicCNF.ProgramSource.sourceTokens decider symbols)

@[simp] theorem directGridUnitsOfSymbols_eq_replicate
    (symbols : List encoding.Γ) :
    directGridUnitsOfSymbols decider symbols =
      List.replicate
        (sourceOrthocrossingGridSize
          (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))
        () := by
  unfold directGridUnitsOfSymbols
  rw [PeriodicCNF.ProgramSource.sourceTokens_eq_requestSource,
    PeriodicCNF.StripGridUnitTokens.gridUnits_requestSource,
    sourceOrthocrossingGridSize_formulaOfSymbols]
  rfl

@[simp] theorem directGridUnitsOfSymbols_length
    (symbols : List encoding.Γ) :
    (directGridUnitsOfSymbols decider symbols).length =
      sourceOrthocrossingGridSize
        (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols) := by
  rw [directGridUnitsOfSymbols_eq_replicate]
  simp

end PeriodicCNFStripReduction
end LeanTrominoes
