/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATComponentVerification
import LeanTrominoes.PeriodicExactOneThreePolySpaceMembership

/-! # Space-certified formula and geometry checks for all four 1D variants

These are components of the supplied-drawing languages. The incidence and
intrinsic grid-bound guards are not included in these predicates.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
open PeriodicCNF

noncomputable def ordinary : FormulaVerifier :=
  ⟨FieldWidth.decideCode,FieldWidth.result,FieldWidth.spacePolynomial,
    FieldWidth.decide_eval,FieldWidth.decide_fits⟩

noncomputable def ordinaryThree : FormulaVerifier :=
  ⟨FieldOccurrences.decideCode,FieldOccurrences.result,FieldOccurrences.spacePolynomial,
    FieldOccurrences.decide_eval,FieldOccurrences.decide_fits⟩

noncomputable def exactOne : FormulaVerifier :=
  ⟨ExactOneFieldSavitch.decideCode,ExactOneFieldSavitch.result,ExactOneFieldSavitch.spacePolynomial,
    ExactOneFieldSavitch.decide_eval,ExactOneFieldSavitch.decide_fits⟩

noncomputable def exactOneThree : FormulaVerifier :=
  ⟨ExactOneFieldOccurrences.decideCode,ExactOneFieldOccurrences.result,ExactOneFieldOccurrences.spacePolynomial,
    ExactOneFieldOccurrences.decide_eval,ExactOneFieldOccurrences.decide_fits⟩

theorem ordinary_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => LocalPeriodicThreeCNF1DSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨ordinary.decider FieldWidth.result_correct⟩

theorem ordinaryThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => LocalPeriodicThreeSATThree1DSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨ordinaryThree.decider FieldOccurrences.result_correct⟩

theorem exactOne_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => PeriodicExactOneCNF.LocalOneDimensionalThreeSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨exactOne.decider ExactOneFieldSavitch.result_correct⟩

theorem exactOneThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨exactOneThree.decider ExactOneFieldOccurrences.result_correct⟩

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
