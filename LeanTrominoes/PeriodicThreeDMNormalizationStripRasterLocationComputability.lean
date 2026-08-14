/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterLocationComputability
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompiler

/-! # Primitive-recursive rectangular raster locations -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxRecDepth 10000

/-- The reflected, horizontally reduced rectangular raster location is
primitive recursive. -/
theorem stripRasterLocation_primrec :
    Primrec fun input : Nat × Cell =>
      stripRasterLocation input.1 input.2 := by
  have horizontal : Primrec fun input : Nat × Cell =>
      input.2.1 % (input.1 : Int) :=
    (intEmodNat_primrec.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst).of_eq
        fun input => intEmodNat_eq input.2.1 input.1
  have twicePeriod : Primrec fun input : Nat × Cell =>
      (2 : Int) * (input.1 : Int) :=
    int_multiply_primrec.comp (Primrec.const 2)
      (int_ofNat_primrec.comp Primrec.fst)
  have vertical : Primrec fun input : Nat × Cell =>
      2 * (input.1 : Int) - input.2.2 :=
    int_subtract_primrec.comp twicePeriod
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.pair horizontal vertical).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
