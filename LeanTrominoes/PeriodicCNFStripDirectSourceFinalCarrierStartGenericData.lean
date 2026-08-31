/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartData
import LeanTrominoes.RetainedAngularFanFinalCarrierStartData

/-! # Generic structural start of direct final carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartGenericDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Generic named start specialized to the direct source and structural base
equality. -/
def directSourceFinalCarrierGenericStructuralStart
    (symbols : List encoding.Γ) : Nat :=
  @finalCarrierStart (ThreeCNFVariable Nat)
    directSourceFinalStructuralBaseDecidableEq
    (directThreeCNFSourceFormula decider symbols)

/-- Equality-explicit generic start specialized to the direct source. -/
def directSourceFinalCarrierGenericFamilyStart
    (symbols : List encoding.Γ) : Nat :=
  @finalCarrierStartFamily (ThreeCNFVariable Nat)
    directSourceFinalStructuralBaseDecidableEq
    (directThreeCNFSourceFormula decider symbols)
    directSourceFinalStructuralVariableDecidableEq

/-- Explicit raw crossover-prefix computation shared by the direct structural
and generic named starts. -/
def directSourceFinalCarrierStructuralRawStart
    (symbols : List encoding.Γ) : Nat :=
  (@crossoverMetadataNormalizedClausesDedup Variable
    directSourceFinalStructuralVariableDecidableEq
      (PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols))).length

/-- The same raw crossover computation with the formula's base equality fixed
to the structural implementation used by the generic family. -/
def directSourceFinalCarrierGenericRawStart
    (symbols : List encoding.Γ) : Nat :=
  (@crossoverMetadataNormalizedClausesDedup Variable
    directSourceFinalStructuralVariableDecidableEq
      (@PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
        directSourceFinalStructuralBaseDecidableEq
        (directThreeCNFSourceFormula decider symbols))).length

/-- Opaque one-sided unfolding of the direct structural start. -/
structure DirectSourceFinalCarrierStructuralStartRaw
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStructuralStart decider symbols =
    directSourceFinalCarrierStructuralRawStart decider symbols

/-- Opaque unfolding from the named generic start to its equality-explicit
family. -/
structure DirectSourceFinalCarrierGenericStartFamily
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierGenericStructuralStart decider symbols =
    directSourceFinalCarrierGenericFamilyStart decider symbols

/-- Opaque unfolding from the equality-explicit generic family to the shared
raw computation. -/
structure DirectSourceFinalCarrierGenericFamilyStartRaw
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierGenericFamilyStart decider symbols =
    directSourceFinalCarrierGenericRawStart decider symbols

/-- Opaque equality transport between the original and structural formula-base
equality implementations. -/
structure DirectSourceFinalCarrierStructuralRawStartEquality
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStructuralRawStart decider symbols =
    directSourceFinalCarrierGenericRawStart decider symbols

/-- Opaque one-sided unfolding of the generic named start. -/
structure DirectSourceFinalCarrierGenericStartRaw
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierGenericStructuralStart decider symbols =
    directSourceFinalCarrierGenericRawStart decider symbols

/-- Opaque certificate identifying the direct structural and generic starts. -/
structure DirectSourceFinalCarrierStartGeneric
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStructuralStart decider symbols =
    directSourceFinalCarrierGenericStructuralStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
