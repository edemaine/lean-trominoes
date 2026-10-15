/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMGraphOrientationEncodingCorrect
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationCompilerComputability
import LeanTrominoes.ThreeDM.PeriodicWangPlanarThreeDMReduction
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationCoRE
import Lean.Util.CollectAxioms

/-! # Completeness of general plane periodic trichromatic orientation

The reduction emits ordinary vertex-kind and colored-edge lists. It does
not carry an orientation-equivalence hypothesis or a supplied drawing.
-/
namespace LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
open Gadget NormalizationCompiler
set_option maxHeartbeats 800000

theorem vertexKind_primrec : Primrec vertexKind := by
  exact (Primrec.sumCasesOn PeriodicThreeDMVertex.equivData_primrec
    (Primrec.const true).to₂ (Primrec.const false).to₂).of_eq fun vertex => by
      cases vertex <;> rfl

theorem edgeRecord_primrec : Primrec₂ edgeRecord := by
  have data : Primrec fun p : PeriodicThreeDM × ContractedEdge =>
      PeriodicEdge.equivData p.2.toPeriodicEdge :=
    (Primrec.of_equiv : Primrec (@PeriodicEdge.equivData PeriodicThreeDMVertex)).comp
      (contractedEdge_toPeriodicEdge_primrec.comp Primrec.snd)
  have vertices : Primrec fun p : PeriodicThreeDM × ContractedEdge =>
      p.1.contractedGraph.vertices := contractedGraphVertices_primrec.comp Primrec.fst
  have source := Primrec.list_idxOf.comp (Primrec.fst.comp data) vertices
  have target := Primrec.list_idxOf.comp (Primrec.fst.comp (Primrec.snd.comp data)) vertices
  have offset := Primrec.snd.comp (Primrec.snd.comp data)
  exact (Primrec.pair
    ((Primrec.of_equiv_symm : Primrec (@PeriodicEdge.equivData Nat).symm).comp
      (Primrec.pair source (Primrec.pair target offset)))
    (contractedEdge_color_primrec.comp Primrec.snd)).of_eq (fun _ => rfl)

private theorem kinds_primrec : Primrec fun p : PeriodicThreeDM =>
    p.contractedGraph.vertices.map vertexKind :=
  Primrec.list_map contractedGraphVertices_primrec (vertexKind_primrec.comp Primrec.snd).to₂

private theorem records_primrec : Primrec fun p : PeriodicThreeDM =>
    p.contractedEdges.map (edgeRecord p) :=
  Primrec.list_map contractedEdges_primrec edgeRecord_primrec

theorem input_primrec : Primrec input := by
  exact (Primrec.pair
    kinds_primrec records_primrec).of_eq (fun _ => rfl)

end LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding

namespace LeanTrominoes.TrichromaticGraphOrientation

noncomputable def wangReduction (tiles : LeanWang.TileSet) : Input :=
  PeriodicThreeDM.GraphOrientationEncoding.input (PeriodicWangPlanarThreeDMReduction.problem tiles)

theorem wangReduction_computable : Computable wangReduction :=
  PeriodicThreeDM.GraphOrientationEncoding.input_primrec.to_comp.comp
    PeriodicWangPlanarThreeDMReduction.problem_computable

theorem wangReduction_correct (tiles : LeanWang.TileSet) :
    Problem (wangReduction tiles) ↔ LeanWang.TilesPlane tiles := by
  rw [wangReduction,PeriodicThreeDM.GraphOrientationEncoding.problem_iff
    _ (PeriodicWangPlanarThreeDMReduction.presentation tiles).problemWellFormed
      (PeriodicWangPlanarThreeDMReduction.problem_degreeTwoOrThree tiles)]
  exact (PeriodicWangPlanarThreeDMReduction.problem_correct tiles).symm

theorem problem_coREHard : LeanWang.CoREHard Problem := by
  intro A _ source hs
  obtain ⟨f,hf,correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨wangReduction ∘ f,wangReduction_computable.comp hf,?_⟩
  intro a
  exact (correct a).trans (wangReduction_correct (f a)).symm

theorem problem_coREComplete : LeanWang.CoREComplete Problem :=
  ⟨problem_coRE,problem_coREHard⟩

open Lean Elab Command in
run_cmd do
  let name := ``problem_coREComplete
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.TrichromaticGraphOrientation
