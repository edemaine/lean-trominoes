/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATCoRE
import LeanTrominoes.PeriodicGraphDrawingSearch
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction
import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedRoutesComputability

/-! # Plane planar 3SAT completeness with checked drawing data -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.WangReduction
open PeriodicOrthocrossing PeriodicGridDrawing.FiniteCertificate
open PeriodicWangPlanarThreeDMReduction
attribute [-instance] drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000
abbrev TargetVariable := WrappedPeriodicPlanarSATVariable Variable
local instance : DecidableEq TargetVariable := by
  unfold TargetVariable
  infer_instance

def formula (tiles : LeanWang.TileSet) : PeriodicCNF TargetVariable :=
  retainedPlanarSATFormula (sourceFormula tiles)

theorem formula_computable : Computable formula :=
  retainedPlanarSATFormula_primrec.to_comp.comp sourceFormula_computable

private theorem certificate (tiles : LeanWang.TileSet) :
    RetainedPlanarSATCertificate (sourceFormula tiles) :=
  retainedPlanarSATCertificate _ (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

private theorem available_generic {V : Type} [Primcodable V] [DecidableEq V]
    (source : PeriodicCNF V) (c : RetainedPlanarSATCertificate source) :
    ∃ d, PeriodicGridDrawing.FiniteCertificate.Valid
      (retainedPlanarSATFormula source).incidenceGraph d := by
  refine ⟨retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing source, ?_⟩
  exact valid_complete c.drawingCompatible
    (PeriodicGridDrawing.segmentEndpointsInExpandedSquare_of_routePoints c.routePointsInside)
    c.drawingRibbonReady.1

theorem available (tiles : LeanWang.TileSet) :
    ∃ d, PeriodicGridDrawing.FiniteCertificate.Valid (formula tiles).incidenceGraph d :=
  available_generic (sourceFormula tiles) (certificate tiles)

def input (tiles : LeanWang.TileSet) : Input TargetVariable :=
  (formula tiles,search (fun ts => (formula ts).incidenceGraph) available tiles)

theorem input_computable : Computable input :=
  Computable.pair formula_computable
    (search_computable (PeriodicCNF.incidenceGraph_computable.comp formula_computable) available)

theorem correct (tiles : LeanWang.TileSet) : LeanWang.TilesPlane tiles ↔ Problem (input tiles) := by
  have semantics : (formula tiles).Satisfiable ↔ LeanWang.TilesPlane tiles :=
    (certificate tiles).sourceSatisfiableIff.trans (sourceFormula_correct tiles).symm
  constructor
  · intro h
    exact ⟨⟨(certificate tiles).widthAtMostThree,search_spec _ available tiles⟩,semantics.2 h⟩
  · intro h; exact semantics.1 h.2

/-- Plane periodic 3SAT is co-r.e. complete with a checked continuous planar
 drawing. The stronger locality, degree-three, and grid-size clauses are separate. -/
theorem coREComplete : LeanWang.CoREComplete (Problem (V := TargetVariable)) := by
  refine ⟨problem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (correct (f a))⟩

attribute [instance] drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq

end LeanTrominoes.PeriodicPlanarSAT.WangReduction
