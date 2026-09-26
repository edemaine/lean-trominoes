/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMGeometry
import LeanTrominoes.PeriodicThreeDMIncidenceCoverage
import LeanTrominoes.UnaryColumnSignedCoordinateSum

/-! # Recovering canonical element positions from incidence route endpoints -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn DelimitedDirectionDisplacement
private theorem targetCoordinate_eq (p : PeriodicThreeDM) (d : PeriodicGridDrawing)
    (tag : IncidenceTag) (e : WireColor × Nat) (h : p.incidenceElement tag = e) (horizontal : Bool) :
    (component horizontal (d.vertexPosition p.incidenceGraph
      (.element tag.color ((p.triples.getD tag.tripleIndex default).reference tag.color).atom))).toNat =
    (component horizontal (d.vertexPosition p.incidenceGraph (.element e.1 e.2))).toNat := by
  exact congrArg (fun e => (component horizontal
    (d.vertexPosition p.incidenceGraph (.element e.1 e.2))).toNat) h

private theorem targetCoordinate_congr (p : PeriodicThreeDM) (d : PeriodicGridDrawing)
    (a b : IncidenceTag) (h : p.incidenceElement a = p.incidenceElement b) (horizontal : Bool) :
    (component horizontal (d.vertexPosition p.incidenceGraph
      (.element a.color ((p.triples.getD a.tripleIndex default).reference a.color).atom))).toNat =
    (component horizontal (d.vertexPosition p.incidenceGraph
      (.element b.color ((p.triples.getD b.tripleIndex default).reference b.color).atom))).toNat :=
  targetCoordinate_eq p d a (p.incidenceElement b) h horizontal

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMTarget_recovery (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) (horizontal : Bool) :
    (component horizontal (nativeThreeDMSourcePoint decider s tag) +
      displacement horizontal (unitSubdivisionDirections (nativeThreeDMRoute decider s tag))) %
      (nativeThreeDMPeriod decider s:Int) = component horizontal (nativeThreeDMTargetPoint decider s tag) := by
  have endpoints := nativeThreeDMRoute_endpoints decider s tag ht
  apply translatedEndpoint_position horizontal _ _ _ _ _ endpoints.1 endpoints.2
    (nativeThreeDMRoute_orthogonal decider s tag ht)
  have inside := nativeThreeDMTargetPoint_inside decider s tag ht
  rw [PeriodicGridDrawing.PositionInFundamentalSquare,nativeThreeDMDrawing_period] at inside
  cases horizontal <;> simp only [component] <;> omega

def nativeThreeDMTargetCoordinateCompiler (horizontal : Bool) :
    Compiler (nativeThreeDMIncidences decider) (fun s tag =>
      (component horizontal (nativeThreeDMTargetPoint decider s tag)).toNat) := by
  let physical := signedSumRemainder
    (nativeThreeDMSourcePointCompiler decider horizontal true)
    (nativeThreeDMSourcePointCompiler decider horizontal false)
    (nativeThreeDMDisplacementCompiler decider horizontal true)
    (nativeThreeDMDisplacementCompiler decider horizontal false)
    (nativeThreeDMPeriodCompiler decider) (nativeThreeDMPeriod_positive decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro tag ht
  exact congrArg Int.toNat (nativeThreeDMTarget_recovery decider s tag ht horizontal)

abbrev nativeThreeDMElementPoint (s : List encoding.Γ) (e : WireColor × Nat) :=
  (nativeThreeDMDrawing decider s).vertexPosition (nativeThreeDMProblem decider s).incidenceGraph
    (.element e.1 e.2)

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMDegree (s : List encoding.Γ) : (nativeThreeDMProblem decider s).DegreeTwoOrThree := by
  rw [nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact problem_degreeTwoOrThree _

def nativeThreeDMElementCoordinateCompiler (horizontal : Bool) :
    Compiler (nativeThreeDMElements decider) (fun s e =>
      (component horizontal (nativeThreeDMElementPoint decider s e)).toNat) := by
  apply keyedRelation (nativeThreeDMElementKeyCompiler decider)
    (nativeThreeDMIncidenceKeyCompiler decider) (nativeThreeDMTargetCoordinateCompiler decider horizontal)
  · intro s a ha b hb eq
    have unique := directSourceFinalCanonicalElementCodes_nodup decider s
    rw [directSourceFinalCanonicalElementCodes_eq_horizontal] at unique
    have same : (nativeThreeDMProblem decider s).incidenceElement a =
        (nativeThreeDMProblem decider s).incidenceElement b := List.inj_on_of_nodup_map unique
      (nativeThreeDMIncidenceElement_mem decider s a ha)
      (nativeThreeDMIncidenceElement_mem decider s b hb) eq
    exact targetCoordinate_congr (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s) a b same horizontal
  · intro s e he
    obtain ⟨tag,ht,equal⟩ := incidenceElement_surjective_of_degreeTwoOrThree
      (nativeThreeDMProblem decider s) (nativeThreeDMDegree decider s) e.1 e.2
      ((nativeThreeDMElement_mem decider s e).1 he)
    exact ⟨tag,ht,congrArg (directSourceFinalHorizontalElementCode decider s) equal⟩
  · intro s e he tag ht eq
    have same := (directSourceFinalHorizontalIncidenceCode_eq_iff decider s e
      ((nativeThreeDMElement_mem decider s e).1 he) tag ht).1 eq
    exact targetCoordinate_eq (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s) tag e same horizontal

end LeanTrominoes.PeriodicCNFStripReduction
end
