/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingFiniteCheck
import LeanTrominoes.PeriodicPlanarSATOneDimensional
import LeanTrominoes.PeriodicExactOneCNFLocality

/-! # Executable decisions for all four supplied-drawing 1D SAT languages

These are semantic decision procedures. Native encoded space bounds are
separate from termination and correctness of the finite searches here.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.LineDecision
variable {V : Type} [DecidableEq V]

private instance widthDecidable (f : PeriodicCNF V) : Decidable (f.WidthAtMost 3) := by
  unfold PeriodicCNF.WidthAtMost PeriodicClause.WidthAtMost
  infer_instance
private instance gridDecidable (coefficient : Nat) (i : Input V) : Decidable (GridBound coefficient i) := by
  unfold GridBound
  infer_instance
private instance routesDecidable (g : PeriodicGraph V) (d : PeriodicGridDrawing) : Decidable (d.RoutesMatch g) := by
  unfold PeriodicGridDrawing.RoutesMatch
  infer_instance
private instance orbitDecidable (g : PeriodicGraph V) (d : PeriodicGridDrawing) :
    Decidable (PeriodicGridDrawing.OrbitCertificate.Compatible g d) := by
  unfold PeriodicGridDrawing.OrbitCertificate.Compatible
  infer_instance
private instance finiteDecidable (g : PeriodicGraph V) (d : PeriodicGridDrawing) :
    Decidable (PeriodicGridDrawing.FiniteCertificate.Compatible g d) := by
  unfold PeriodicGridDrawing.FiniteCertificate.Compatible PeriodicGridDrawing.PositionInFundamentalSquare
  infer_instance

def ordinaryCheck (i : Input V) : Bool :=
  decide (GridBound 8847360 i) && decide (i.1.WidthAtMost 3) &&
    decide (PeriodicGridDrawing.OrbitCertificate.Compatible i.1.incidenceGraph i.2) &&
    PeriodicGridDrawing.FiniteBounds.check i.2 && PeriodicCNF.LineWindow.check i.1

def ordinaryThreeCheck (i : Input V) : Bool :=
  PeriodicExactOneCNF.occurrenceCheck i.1 && ordinaryCheck i

def exactOneCheck (i : Input V) : Bool :=
  decide (GridBound 637009920 i) &&
    decide (PeriodicGridDrawing.FiniteCertificate.Compatible i.1.incidenceGraph i.2) &&
    PeriodicGridDrawing.FiniteBounds.check i.2 && PeriodicExactOneCNF.checkThree i.1

def exactOneThreeCheck (i : Input V) : Bool :=
  PeriodicExactOneCNF.occurrenceCheck i.1 && exactOneCheck i

theorem ordinaryCheck_correct (i : Input V) :
    ordinaryCheck i = true ↔ Orbit.LocalOneDimensionalProblem i := by
  simp only [ordinaryCheck,Bool.and_eq_true,decide_eq_true_eq,
    PeriodicGridDrawing.FiniteBounds.check_correct,PeriodicCNF.LineWindow.check_correct,
    Orbit.LocalOneDimensionalProblem,Orbit.BoundedLocalProblem,Orbit.LocalProblem,Orbit.Problem,Orbit.Valid]
  tauto

theorem ordinaryThreeCheck_correct (i : Input V) :
    ordinaryThreeCheck i = true ↔ Orbit.LocalOneDimensionalThreeOccurrenceProblem i := by
  simp only [ordinaryThreeCheck,Bool.and_eq_true,PeriodicExactOneCNF.occurrenceCheck_correct,
    ordinaryCheck_correct,Orbit.LocalOneDimensionalProblem,Orbit.LocalOneDimensionalThreeOccurrenceProblem,
    Orbit.BoundedLocalProblem,Orbit.BoundedLocalThreeOccurrenceProblem,Orbit.LocalProblem,
    Orbit.LocalThreeOccurrenceProblem,Orbit.ThreeOccurrenceProblem]
  tauto

theorem exactOneCheck_correct (i : Input V) :
    exactOneCheck i = true ↔ Unbounded.LocalOneDimensionalExactOneProblem i := by
  simp only [exactOneCheck,Bool.and_eq_true,decide_eq_true_eq,
    PeriodicGridDrawing.FiniteBounds.check_correct,PeriodicExactOneCNF.checkThree_correct,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSAT,PeriodicExactOneCNF.LocalOneDimensionalSAT,
    Unbounded.LocalOneDimensionalExactOneProblem,Unbounded.BoundedLocalExactOneProblem,
    Unbounded.LocalExactOneProblem,Unbounded.ExactOneProblem,Unbounded.Valid]
  tauto

theorem exactOneThreeCheck_correct (i : Input V) :
    exactOneThreeCheck i = true ↔ Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem i := by
  simp only [exactOneThreeCheck,Bool.and_eq_true,PeriodicExactOneCNF.occurrenceCheck_correct,
    exactOneCheck_correct,Unbounded.LocalOneDimensionalExactOneProblem,
    Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,Unbounded.BoundedLocalExactOneProblem,
    Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,Unbounded.LocalExactOneProblem,
    Unbounded.LocalExactOneThreeOccurrenceProblem,Unbounded.ExactOneThreeOccurrenceProblem]
  tauto

end LeanTrominoes.PeriodicPlanarSAT.LineDecision
