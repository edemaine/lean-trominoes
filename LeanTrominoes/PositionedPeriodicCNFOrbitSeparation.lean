/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphOrbitCertificate

/-! # Assembling vertex-orbit separation for positioned CNF -/
namespace LeanTrominoes.PositionedPeriodicCNF
open PeriodicGridDrawing.OrbitCertificate
variable {V : Type} [DecidableEq V]

theorem incidenceVertexResidues_nodup (f : PositionedPeriodicCNF V)
    (p : PeriodicVariablePlacement V)
    (variableSeparation : ∀ a ∈ f.erase.variableOccurrences, ∀ b ∈ f.erase.variableOccurrences,
      ∀ t, p.position a = Cell.add (p.translation t) (p.position b) → a = b)
    (clauses : ∀ c i, (c,i) ∈ f.clauses.zipIdx → ∀ e j, (e,j) ∈ f.clauses.zipIdx →
      ∀ t, c.position = Cell.add (p.translation t) e.position → i = j)
    (mixed : ∀ a ∈ f.erase.variableOccurrences, ∀ c i, (c,i) ∈ f.clauses.zipIdx →
      ∀ t, c.position ≠ Cell.add (p.translation t) (p.position a)) :
    ((f.incidenceVertexPositions p).map (residue p.period)).Nodup := by
  let vp := fun a => residue p.period (p.position a)
  let cp := fun c => residue p.period (canonicalClausePosition p c)
  have vn : (f.erase.variableOccurrences.dedup.map vp).Nodup := by
    apply (List.nodup_dedup _).map_on
    intro a ha b hb eq
    obtain ⟨t,ht⟩ := (residue_eq_iff p.period _ _).1 eq
    exact variableSeparation a (List.mem_dedup.mp ha) b (List.mem_dedup.mp hb) t ht
  have canonical_to_stored (c e : PositionedPeriodicClause V) (t : Cell)
      (eq : canonicalClausePosition p c = Cell.add (p.translation t) (canonicalClausePosition p e)) :
      c.position = Cell.add (p.translation
        (Cell.add t (Cell.sub (PeriodicCNF.clauseAnchor c.literals) (PeriodicCNF.clauseAnchor e.literals)))) e.position := by
    apply Prod.ext <;> simp only [canonicalClausePosition,PeriodicVariablePlacement.translation,
      Cell.add,Cell.sub,Cell.scale,Prod.mk.injEq] at eq ⊢ <;> nlinarith [eq.1,eq.2]
  have cn : (f.clauses.map cp).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j eq
    apply Fin.ext
    obtain ⟨t,ht⟩ := (residue_eq_iff p.period _ _).1 (by simpa [cp] using eq)
    apply clauses _ i.val (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem (by simpa using i.isLt)))
      _ j.val (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem (by simpa using j.isLt)))
    exact canonical_to_stored _ _ t ht
  have dis : List.Disjoint (f.erase.variableOccurrences.dedup.map vp) (f.clauses.map cp) := by
    rw [List.disjoint_left]
    intro x hv hc
    obtain ⟨a,ha,ax⟩ := List.mem_map.mp hv
    obtain ⟨c,hc,cx⟩ := List.mem_map.mp hc
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hc
    have eq : cp c = vp a := cx.trans ax.symm
    obtain ⟨t,ht⟩ := (residue_eq_iff p.period _ _).1 eq
    apply mixed a (List.mem_dedup.mp ha) c i (List.mem_zipIdx_iff_getElem?.mpr hi)
      (Cell.add t (PeriodicCNF.clauseAnchor c.literals))
    apply Prod.ext <;> simp only [canonicalClausePosition,PeriodicVariablePlacement.translation,
      Cell.add,Cell.sub,Cell.scale,Prod.mk.injEq] at ht ⊢ <;> nlinarith [ht.1,ht.2]
  have joined := vn.append cn dis
  simpa only [incidenceVertexPositions,PeriodicCNF.incidenceVariableVertices,List.map_append,
    List.map_map,Function.comp_def,vp,cp] using joined
theorem orbitCompatible_of (f : PositionedPeriodicCNF V) (p : PeriodicVariablePlacement V)
    (routes : IncidenceRoutes) (hp : 0 < p.period)
    (hn : ((f.incidenceVertexPositions p).map (residue p.period)).Nodup)
    (hr : (incidenceDrawing f p routes).RoutesMatch f.erase.incidenceGraph) :
    PeriodicGridDrawing.OrbitCertificate.Compatible f.erase.incidenceGraph (incidenceDrawing f p routes) := by
  refine ⟨incidenceVertexPositions_length f p,incidenceEdgeRoutes_length f routes,?_,hr⟩
  change ((f.incidenceVertexPositions p).map (residue (incidenceDrawing f p routes).gridSize)).Nodup
  rw [incidenceDrawing_gridSize f p routes hp]
  exact hn

end LeanTrominoes.PositionedPeriodicCNF
