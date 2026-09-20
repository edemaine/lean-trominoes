/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphDrawingCertificate
import LeanWang.CoRE

/-! # Effective universal tests for periodic drawing planarity

No bounding box for stored routes is required here. Nonplanarity is witnessed
by finitely many segment indices and integer translations (and, for the
integer-grid contact condition, an integer point).
-/
namespace LeanTrominoes.PeriodicGridDrawing.PlanaritySearch
open Computability
set_option maxHeartbeats 1000000
abbrev Probe := Cell × Cell × Cell
abbrev Data := PeriodicGridDrawing × Probe

def pairCheck (i : (Data × IndexedGridSegment) × IndexedGridSegment) : Prop :=
  let d := i.1.1.1
  let p := i.1.1.2
  let a := i.1.2
  let b := i.2
  SegmentOccurrenceKey a p.1 = SegmentOccurrenceKey b p.2.1 ∨
    (¬ ((a.segment.translate (d.periodTranslation p.1)).InteriorContains p.2.2 ∧
      (b.segment.translate (d.periodTranslation p.2.1)).Contains p.2.2)) ∧
    ¬ GridSegment.InteriorsMeet (a.segment.translate (d.periodTranslation p.1))
      (b.segment.translate (d.periodTranslation p.2.1))

def vertexCheck (i : (Data × Cell) × IndexedGridSegment) : Prop :=
  ¬ (i.2.segment.translate (i.1.1.1.periodTranslation i.1.1.2.2.1)).InteriorContains
    (Cell.add i.1.2 (i.1.1.1.periodTranslation i.1.1.2.1))

def At (d : PeriodicGridDrawing) (p : Probe) : Prop :=
  (∀ a ∈ d.indexedSegments, ∀ b ∈ d.indexedSegments, pairCheck (((d,p),a),b)) ∧
  (∀ v ∈ d.vertexPositions, ∀ s ∈ d.indexedSegments, vertexCheck (((d,p),v),s))

theorem all_iff (d : PeriodicGridDrawing) : (∀ p, At d p) ↔ d.IsContinuouslyPlanar := by
  classical
  constructor
  · intro h
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro a ha b hb t u p ne interior contains
      rcases (h (t,u,p)).1 a ha b hb with eq | separated
      · exact ne eq
      · exact separated.1 ⟨interior,contains⟩
    · intro v hv s hs t u
      exact (h (t,u,(0,0))).2 v hv s hs
    · intro a ha b hb t u ne
      rcases (h (t,u,(0,0))).1 a ha b hb with eq | separated
      · exact False.elim (ne eq)
      · exact separated.2
  · intro h p
    constructor
    · intro a ha b hb
      by_cases eq : SegmentOccurrenceKey a p.1 = SegmentOccurrenceKey b p.2.1
      · exact Or.inl eq
      · exact Or.inr ⟨fun contact => h.1.1 a ha b hb p.1 p.2.1 p.2.2 eq contact.1 contact.2,
          h.2 a ha b hb p.1 p.2.1 eq⟩
    · intro v hv s hs
      exact h.1.2 v hv s hs p.1 p.2.1

private theorem pairCheck_primrec : PrimrecPred pairCheck := by
  let d : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let p : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let a : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.2) :=
    Primrec.snd.comp Primrec.fst
  let t : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.1.2.1) := Primrec.fst.comp p
  let u : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp p)
  let point : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment => i.1.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp p)
  let first : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment =>
      i.1.2.segment.translate (i.1.1.1.periodTranslation i.1.1.2.1)) := GridSegment.translate_primrec.comp (periodTranslation_primrec.comp d t)
    (IndexedGridSegment.segment_primrec.comp a)
  let second : Primrec (fun i : (Data × IndexedGridSegment) × IndexedGridSegment =>
      i.2.segment.translate (i.1.1.1.periodTranslation i.1.1.2.2.1)) := GridSegment.translate_primrec.comp (periodTranslation_primrec.comp d u)
    (IndexedGridSegment.segment_primrec.comp Primrec.snd)
  exact (Primrec.eq.comp (segmentOccurrenceKey_primrec.comp a t)
    (segmentOccurrenceKey_primrec.comp Primrec.snd u)).or
    (((GridSegment.interiorContains_primrec.comp first point).and
      (GridSegment.contains_primrec.comp second point)).not.and
      (GridSegment.interiorsMeet_primrec.comp first second).not)

private theorem vertexCheck_primrec : PrimrecPred vertexCheck := by
  let d : Primrec (fun i : (Data × Cell) × IndexedGridSegment => i.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let p : Primrec (fun i : (Data × Cell) × IndexedGridSegment => i.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let t : Primrec (fun i : (Data × Cell) × IndexedGridSegment => i.1.1.2.1) := Primrec.fst.comp p
  let u : Primrec (fun i : (Data × Cell) × IndexedGridSegment => i.1.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp p)
  exact (GridSegment.interiorContains_primrec.comp
    (GridSegment.translate_primrec.comp (periodTranslation_primrec.comp d u)
      (IndexedGridSegment.segment_primrec.comp Primrec.snd))
    (cell_add_primrec.comp (Primrec.snd.comp Primrec.fst) (periodTranslation_primrec.comp d t))).not

theorem at_primrec : PrimrecRel At := by
  have row : PrimrecPred fun i : Data × IndexedGridSegment =>
      ∀ s ∈ i.1.1.indexedSegments, pairCheck (i,s) :=
    primrecPred_forall_mem (indexedSegments_primrec.comp (Primrec.fst.comp Primrec.fst))
      pairCheck_primrec.primrecRel
  have pairs := primrecPred_forall_mem (indexedSegments_primrec.comp Primrec.fst) row.primrecRel
  have vr : PrimrecPred fun i : Data × Cell =>
      ∀ s ∈ i.1.1.indexedSegments, vertexCheck (i,s) :=
    primrecPred_forall_mem (indexedSegments_primrec.comp (Primrec.fst.comp Primrec.fst))
      vertexCheck_primrec.primrecRel
  exact pairs.and (primrecPred_forall_mem (vertexPositions_primrec.comp Primrec.fst) vr.primrecRel)

noncomputable def probeAt (n : Nat) : Probe := (Encodable.decode n).getD ((0,0),(0,0),(0,0))

theorem probeAt_primrec : Primrec probeAt :=
  (Primrec.option_getD (α := Probe)).comp Primrec.decode (Primrec.const ((0,0),(0,0),(0,0)))

@[simp] theorem probeAt_encode (p : Probe) : probeAt (Encodable.encode p) = p := by
  simp only [probeAt,Encodable.encodek,Option.getD_some]

theorem all_nat_iff (d : PeriodicGridDrawing) :
    (∀ n, At d (probeAt n)) ↔ d.IsContinuouslyPlanar := by
  rw [← all_iff]
  exact ⟨fun h p => by simpa only [probeAt_encode] using h (Encodable.encode p),fun h n => h _⟩

theorem coRE : LeanWang.CoREPred IsContinuouslyPlanar := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun (d : PeriodicGridDrawing) n => ¬ At d (probeAt n))
    (at_primrec.comp Primrec.fst (probeAt_primrec.comp Primrec.snd)).not.computablePred
  exact obstruction.of_eq fun d => by
    rw [← not_forall,all_nat_iff]

end LeanTrominoes.PeriodicGridDrawing.PlanaritySearch
