/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationFinalCellTypesComputability

/-! # Computability of the complete normalized drawing compiler -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def compileData (input : Input) :
    Nat × Nat × List OrthogonalCellType :=
  (finalNormalizationPeriod input - 1,
    finalNormalizationPeriod input - 1,
    finalCellTypes input)

theorem compileData_primrec : Primrec compileData := by
  have periodPred : Primrec fun input : Input =>
      finalNormalizationPeriod input - 1 :=
    Primrec.nat_sub.comp finalNormalizationPeriod_primrec
      (Primrec.const 1)
  exact (Primrec.pair periodPred
    (Primrec.pair periodPred finalCellTypes_primrec)).of_eq fun _ => rfl

def periodicOrthogonalDrawingFromData
    (data : Nat × Nat × List OrthogonalCellType) :
    PeriodicOrthogonalDrawing :=
  PeriodicOrthogonalDrawing.equivData.symm data

theorem periodicOrthogonalDrawingFromData_primrec :
    Primrec periodicOrthogonalDrawingFromData := by
  exact Primrec.of_equiv_symm

theorem compile_primrec : Primrec compile :=
  (periodicOrthogonalDrawingFromData_primrec.comp
    compileData_primrec).of_eq fun _ => rfl

theorem compile_computable : Computable compile :=
  compile_primrec.to_comp

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
