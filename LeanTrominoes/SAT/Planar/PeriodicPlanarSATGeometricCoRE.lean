/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricEndpoints
import LeanTrominoes.ThreeDM.PeriodicThreeDMFiniteDrawingCertificateComputability

/-! # Effective universal tests for endpoint-separated orthogonal drawings -/
namespace LeanTrominoes.PeriodicPlanarSAT.GeometricSearch
open LeanTrominoes.Computability
set_option maxHeartbeats 2000000
abbrev Probe := Cell × Cell
abbrev Data := PeriodicGridDrawing × Probe

def pairCheck (i : (Data × IndexedRoutePoint) × IndexedRoutePoint) : Prop :=
  let d := i.1.1.1
  let p := i.1.1.2
  let a := i.1.2
  let b := i.2
  PeriodicGridDrawing.RoutePointOccurrenceKey a p.1 = PeriodicGridDrawing.RoutePointOccurrenceKey b p.2 ∨
    Cell.add a.point (d.periodTranslation p.1)≠Cell.add b.point (d.periodTranslation p.2) ∨
    (a.IsEndpoint ∧ b.IsEndpoint)

def At (d : PeriodicGridDrawing) (p : Probe) : Prop :=
  ∀ a∈d.indexedRoutePoints, ∀ b∈d.indexedRoutePoints, pairCheck (((d,p),a),b)

 theorem all_iff (d : PeriodicGridDrawing) :
    (∀ p, At d p) ↔ d.RoutePointsMeetOnlyAtEndpoints := by
  constructor
  · intro h a ha b hb t u different equal
    rcases h (t,u) a ha b hb with same | unequal | endpoints
    · exact (different same).elim
    · exact (unequal equal).elim
    · exact endpoints
  · intro h p a ha b hb
    by_cases same : PeriodicGridDrawing.RoutePointOccurrenceKey a p.1=PeriodicGridDrawing.RoutePointOccurrenceKey b p.2
    · exact Or.inl same
    · right
      by_cases equal : Cell.add a.point (d.periodTranslation p.1)=Cell.add b.point (d.periodTranslation p.2)
      · exact Or.inr (h a ha b hb p.1 p.2 same equal)
      · exact Or.inl equal

 theorem pairCheck_primrec : PrimrecPred pairCheck := by
  let d : Primrec (fun i : (Data × IndexedRoutePoint) × IndexedRoutePoint => i.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let p : Primrec (fun i : (Data × IndexedRoutePoint) × IndexedRoutePoint => i.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let a : Primrec (fun i : (Data × IndexedRoutePoint) × IndexedRoutePoint => i.1.2) := Primrec.snd.comp Primrec.fst
  let t := Primrec.fst.comp p
  let u := Primrec.snd.comp p
  let first := cell_add_primrec.comp (IndexedRoutePoint.point_primrec.comp a)
    (PeriodicGridDrawing.periodTranslation_primrec.comp d t)
  let second := cell_add_primrec.comp (IndexedRoutePoint.point_primrec.comp Primrec.snd)
    (PeriodicGridDrawing.periodTranslation_primrec.comp d u)
  exact (Primrec.eq.comp (PeriodicGridDrawing.routePointOccurrenceKey_primrec.comp a t)
    (PeriodicGridDrawing.routePointOccurrenceKey_primrec.comp Primrec.snd u)).or
    ((Primrec.eq.comp first second).not.or
      ((IndexedRoutePoint.isEndpoint_primrec.comp a).and (IndexedRoutePoint.isEndpoint_primrec.comp Primrec.snd)))

 theorem at_primrec : PrimrecRel At := by
  have row : PrimrecPred fun i : Data × IndexedRoutePoint =>
      ∀ b∈i.1.1.indexedRoutePoints, pairCheck (i,b) :=
    primrecPred_forall_mem (PeriodicGridDrawing.indexedRoutePoints_primrec.comp (Primrec.fst.comp Primrec.fst))
      pairCheck_primrec.primrecRel
  exact primrecPred_forall_mem (PeriodicGridDrawing.indexedRoutePoints_primrec.comp Primrec.fst) row.primrecRel

noncomputable def probeAt (n : ℕ) : Probe := (Encodable.decode n).getD ((0,0),(0,0))
 theorem probeAt_primrec : Primrec probeAt :=
  (Primrec.option_getD (α:=Probe)).comp Primrec.decode (Primrec.const ((0,0),(0,0)))
 @[simp] theorem probeAt_encode (p : Probe) : probeAt (Encodable.encode p)=p := by
  simp only [probeAt,Encodable.encodek,Option.getD_some]
 theorem all_nat_iff (d : PeriodicGridDrawing) :
    (∀ n, At d (probeAt n)) ↔ d.RoutePointsMeetOnlyAtEndpoints := by
  rw [←all_iff]
  exact ⟨fun h p => by simpa only [probeAt_encode] using h (Encodable.encode p),fun h n => h _⟩

 theorem contacts_coRE : LeanWang.CoREPred PeriodicGridDrawing.RoutePointsMeetOnlyAtEndpoints := by
  have obstruction := LeanWang.REPred.exists_nat
    (p:=fun (d : PeriodicGridDrawing) n => ¬At d (probeAt n))
    (at_primrec.comp Primrec.fst (probeAt_primrec.comp Primrec.snd)).not.computablePred
  exact obstruction.of_eq fun d => by rw [←not_forall,all_nat_iff]

 theorem coRE_and {A : Type} [Primcodable A] {p q : A → Prop}
    (hp : LeanWang.CoREPred p) (hq : LeanWang.CoREPred q) : LeanWang.CoREPred (fun a => p a ∧ q a) := by
  classical
  obtain ⟨merged,computable,correct⟩ := Partrec.merge' hp hq
  apply computable.dom_re.of_eq
  intro a
  rw [(correct a).2]
  simp only [Part.assert,Part.some_dom]
  tauto

 theorem orthogonal_coRE : LeanWang.CoREPred PeriodicGridDrawing.IsOrthogonal := by
  have test := (Primrec.eq.comp PeriodicThreeDM.FiniteDrawingCertificate.orthogonalCheck_primrec (Primrec.const true)).not.computablePred.to_re
  apply test.of_eq
  intro drawing
  apply not_congr
  exact ⟨PeriodicThreeDM.FiniteDrawingCertificate.orthogonalCheck_spec,
    PeriodicThreeDM.FiniteDrawingCertificate.orthogonalCheck_complete⟩

 theorem strongGeometry_coRE : LeanWang.CoREPred StrongGeometry :=
  coRE_and orthogonal_coRE (coRE_and PeriodicGridDrawing.PlanaritySearch.coRE contacts_coRE)

 theorem geometric_coRE {V : Type} [Primcodable V] {p : Input V → Prop} (hp : LeanWang.CoREPred p) :
    LeanWang.CoREPred (Geometric p) :=
  coRE_and hp (LeanWang.REPred.comp strongGeometry_coRE Primrec.snd.to_comp)

end LeanTrominoes.PeriodicPlanarSAT.GeometricSearch
