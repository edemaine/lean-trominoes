/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.CompletionCircuitStripCut

/-! # Cut and repeat a circuit across a finite domain with blank seams -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

def cutDomain (inside : Cell → Prop) [DecidablePred inside]
    (kinds : Cell → CircuitKind) (location : Cell) : CircuitKind :=
  if inside location then kinds location else .blank

/-- A blank endpoint on every cut edge makes restricting a satisfying
source to the finite domain exact. -/
theorem source_cutDomain (inside : Cell → Prop) [DecidablePred inside] (kinds : Cell → CircuitKind)
    (boundary : ∀ location port, inside location ≠ inside (gridNeighbor location port) →
      kinds location=.blank ∨ kinds (gridNeighbor location port)=.blank) :
    SourceHolds kinds → SourceHolds (cutDomain inside kinds) := by
  rintro ⟨values,seams,valid⟩
  have blankEdge (location : Cell) (port : Fin 4)
      (different : inside location ≠ inside (gridNeighbor location port)) :
      values location port=false ∧ values (gridNeighbor location port) (gridOpposite port)=false := by
    rcases boundary location port different with blank|blank
    · have left := blank_source_values (by simpa only [blank] using valid location) port
      exact ⟨left,(seams location port).symm.trans left⟩
    · have right := blank_source_values (by simpa only [blank] using valid (gridNeighbor location port)) (gridOpposite port)
      exact ⟨(seams location port).trans right,right⟩
  refine ⟨fun location port => if inside location then values location port else false,?_,?_⟩
  · intro location port
    by_cases first : inside location <;> by_cases second : inside (gridNeighbor location port)
    · simpa only [if_pos first,if_pos second] using seams location port
    · have equal := blankEdge location port (by intro eq;exact second (eq ▸ first))
      simpa only [if_pos first,if_neg second] using equal.1
    · have equal := blankEdge location port (by intro eq;exact first (eq.symm ▸ second))
      simpa only [if_neg first,if_pos second] using equal.2.symm
    · simp only [if_neg first,if_neg second]
  · intro location
    by_cases member : inside location
    · simpa only [cutDomain,if_pos member] using valid location
    · simp [cutDomain,member,CircuitKind.SourceRelation,CircuitKind.portEnabled]

/-- A model on the cut domain repeats correctly whenever each wrapped edge
is either an ordinary edge or joins two ports already capped by blank cells. -/
theorem source_repeat_cutDomain (inside : Cell → Prop) [DecidablePred inside]
    (kinds : Cell → CircuitKind) (wrap : Cell → Cell)
    (insideWrap : ∀ location,inside (wrap location))
    (periodic : ∀ location,kinds (wrap location)=kinds location)
    (adjacent : ∀ location port,
      gridNeighbor (wrap location) port=wrap (gridNeighbor location port) ∨
      (¬inside (gridNeighbor (wrap location) port) ∧
        ¬inside (gridNeighbor (wrap (gridNeighbor location port)) (gridOpposite port)))) :
    SourceHolds (cutDomain inside kinds) → SourceHolds kinds := by
  rintro ⟨values,seams,valid⟩
  have capped (location : Cell) (port : Fin 4) (outside : ¬inside (gridNeighbor location port)) :
      values location port=false := by
    have other := blank_source_values (by
      simpa only [cutDomain,if_neg outside] using valid (gridNeighbor location port)) (gridOpposite port)
    exact (seams location port).trans other
  refine ⟨fun location port => values (wrap location) port,?_,?_⟩
  · intro location port
    rcases adjacent location port with equal|outside
    · simpa only [equal] using seams (wrap location) port
    · exact (capped (wrap location) port outside.1).trans
        (capped (wrap (gridNeighbor location port)) (gridOpposite port) outside.2).symm
  · intro location
    simpa only [cutDomain,if_pos (insideWrap location),periodic] using valid (wrap location)
end LeanTrominoes.CompletionPattern.LBricks.Circuit
