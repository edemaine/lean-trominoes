/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalSourceOrbitSeparation
import LeanTrominoes.PositionedPeriodicCNFOrbitSeparation

/-! # Vertex-orbit compatibility of the ordinary fixed-eight SAT drawing -/
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
open PeriodicOrthocrossing PositionedPeriodicCNF
set_option maxHeartbeats 400000
variable {V : Type} [DecidableEq V]
abbrev Target (V : Type) := ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable V)
abbrev formula (f : PeriodicCNF V) := retainedFigureNineClearancePositionedFormula f
abbrev placement (f : PeriodicCNF V) := retainedFigureNineClearancePlacement f
abbrev routes (f : PeriodicCNF V) := retainedFigureNineClearanceIncidenceRoutes f

private theorem occurrence_witness {A : Type} (f : PositionedPeriodicCNF A) {a : A}
    (ha : a ∈ f.erase.variableOccurrences) :
    ∃ e j l k, (e,j) ∈ f.clauses.zipIdx ∧ (l,k) ∈ e.literals.zipIdx ∧ l.atom = a := by
  unfold PeriodicCNF.variableOccurrences erase at ha
  simp only [List.flatMap_map] at ha
  obtain ⟨e,he,heatom⟩ := List.mem_flatMap.mp ha
  obtain ⟨l,hlit,atomEq⟩ := List.mem_map.mp heatom
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hlit
  exact ⟨e,j,l,k,List.mem_zipIdx_iff_getElem?.mpr hj,List.mem_zipIdx_iff_getElem?.mpr hk,atomEq⟩

private theorem canonical_mixed_shift {A : Type} (p : PeriodicVariablePlacement A)
    (c e : PositionedPeriodicClause A) (l : PeriodicLiteral A) (t : Cell)
    (eq : c.position = Cell.add (p.translation t) (p.position l.atom)) :
    canonicalClausePosition p c = Cell.add
      (p.translation (Cell.add (Cell.sub t (PeriodicCNF.clauseAnchor c.literals))
        (Cell.sub (PeriodicCNF.clauseAnchor e.literals) l.offset)))
      (canonicalLiteralPosition p e l) := by
  have hx := congrArg Prod.fst eq
  have hy := congrArg Prod.snd eq
  apply Prod.ext <;> simp only [canonicalClausePosition,canonicalLiteralPosition,
    PeriodicVariablePlacement.translation,Cell.add,Cell.sub,Cell.scale] at hx hy ⊢ <;> nlinarith

variable (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
  (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ [])
include hl hw ho hn

theorem mixed {a : Target V} (ha : a ∈ (formula f).erase.variableOccurrences)
    {c : PositionedPeriodicClause (Target V)} {i : Nat}
    (hc : (c,i) ∈ (formula f).clauses.zipIdx) (t : Cell) :
    c.position ≠ Cell.add ((placement f).translation t) ((placement f).position a) := by
  intro eq
  rcases exists_clockwiseClause_of_clearanceClause_mem hc with ⟨c₀,hc₀,rfl⟩
  have ha₀ : a ∈ (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula f).erase.variableOccurrences := by
    simpa only [formula,retainedFigureNineClearancePositionedFormula,erase_scale] using ha
  obtain ⟨e,j,l,k,hj,hk,atomEq⟩ := occurrence_witness _ ha₀
  let p := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement f
  have unscaled : c₀.position = Cell.add (p.translation t) (p.position a) := by
    apply Cell.scale_injective (show (retainedFigureNineSourceClearanceFactor : Int) ≠ 0 by decide)
    simpa only [placement,retainedFigureNineClearancePlacement,PeriodicVariablePlacement.scale_position,
      PeriodicVariablePlacement.translation_scale,PositionedPeriodicClause.scale_position,
      Cell.scale_add] using eq
  apply retainedOrderedFixedEightCanonicalClausePosition_ne_translatedLiteralPosition
    f hl hw ho hn hc₀ hj hk
    (Cell.add (Cell.sub t (PeriodicCNF.clauseAnchor c₀.literals))
      (Cell.sub (PeriodicCNF.clauseAnchor e.literals) l.offset))
  exact canonical_mixed_shift p c₀ e l t (by simpa only [atomEq] using unscaled)

theorem residues_nodup :
    (((formula f).incidenceVertexPositions (placement f)).map
      (PeriodicGridDrawing.OrbitCertificate.residue (placement f).period)).Nodup := by
  apply incidenceVertexResidues_nodup
  · intro a ha b hb t eq
    exact retainedFigureNineClearanceVariablePosition_eq_translated_imp_eq f hl hw ho hn ha hb t eq
  · intro c i hc e j he t eq
    exact retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq f hl hw ho hn hc he t eq
  · intro a ha c i hc t
    exact mixed f hl hw ho hn ha hc t

noncomputable def routeCertificate : CanonicalOrthogonalIncidenceRoutes (formula f) (placement f) where
  routes := routes f
  endpoints := by
    intro c i hc l j hlit
    have h := retainedFigureNineClearanceIncidenceRoutes_valid f hl hw ho hn hc hlit
    exact ⟨h.1,h.2.1⟩
  orthogonal := by
    intro c i hc l j hlit
    exact (retainedFigureNineClearanceIncidenceRoutes_valid f hl hw ho hn hc hlit).2.2

def drawing (f : PeriodicCNF V) : PeriodicGridDrawing :=
  incidenceDrawing (formula f) (placement f) (routes f)

theorem compatible : PeriodicGridDrawing.OrbitCertificate.Compatible
    (formula f).erase.incidenceGraph (drawing f) := by
  exact orbitCompatible_of (formula f) (placement f) (routes f)
    (retainedFigureNineClearancePlacement_period_pos f)
    (residues_nodup f hl hw ho hn)
    (by simpa only [routeCertificate] using
      ((routeCertificate f hl hw ho hn).routesMatch
        (retainedFigureNineClearancePlacement_period_pos f)))

theorem planar : (drawing f).IsContinuouslyPlanar := by
  have ready : (drawing f).IsRibbonReady := by
    apply PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    · exact incidenceDrawing_relativeLiftedRoutesAvoidEachOther (formula f) (placement f) (routes f)
        (retainedFigureNineClearancePlacement_period_pos f)
        (retainedFigureNineClearanceIncidenceRoutes_relativeAvoidEachOther f hl hw ho hn)
    · apply incidenceDrawing_routesSimple_of_pointwise
      intro c i hc l j hlit
      exact retainedFigureNineClearanceIncidenceRoutes_isSimple f hl hw ho hn hc hlit
    · apply incidenceDrawing_hasUnitSteps_of_pointwise
      intro c i hc l j hlit
      exact retainedFigureNineClearanceIncidenceRoutes_unitSteps f hl hw ho hn hc hlit
  exact ready.1

end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
