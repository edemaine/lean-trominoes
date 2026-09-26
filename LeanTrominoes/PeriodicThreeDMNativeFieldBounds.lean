/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMLineDecision
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.PeriodicThreeDMIncidenceCoverage

/-! # Polynomial numeric bounds on valid local 3DM instance fields -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

theorem elementCount_le_triples (p : PeriodicThreeDM) (degrees : p.DegreeTwoOrThree) (color : WireColor) :
    p.elementCount color ≤ p.triples.length := by
  have subset : Finset.range (p.elementCount color) ⊆
      (p.triples.map (fun t => (t.reference color).atom)).toFinset := by
    intro atom member
    obtain ⟨tag,ht,equal⟩ := incidenceElement_surjective_of_degreeTwoOrThree p degrees color atom
      (Finset.mem_range.mp member)
    have index := incidenceTag_tripleIndex_lt p ht
    have colorEq : tag.color = color := congrArg Prod.fst equal
    have atomEq : ((p.triples.getD tag.tripleIndex default).reference color).atom = atom := by
      have h := congrArg Prod.snd equal
      simpa only [incidenceElement,colorEq] using h
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨p.triples[tag.tripleIndex],List.getElem_mem index,?_⟩
    simpa only [List.getD_eq_getElem _ _ index] using atomEq
  have card := Finset.card_le_card subset
  have bound := List.toFinset_card_le (p.triples.map (fun t => (t.reference color).atom))
  simp only [Finset.card_range,List.length_map] at card bound
  omega

private theorem encode_small_int (z : Int) (small : z.natAbs ≤ 1) : Encodable.encode z ≤ 2 := by
  have cases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem native_fields_bounded (p : PeriodicThreeDM) (wf : p.IsWellFormed)
    (degrees : p.DegreeTwoOrThree) (locality : p.IsLocal) :
    ∀ n ∈ FlatEncoding.fields p, n < p.triples.length+3 := by
  have red := elementCount_le_triples p degrees .red
  have green := elementCount_le_triples p degrees .green
  have blue := elementCount_le_triples p degrees .blue
  intro n member
  simp only [FlatEncoding.fields,List.mem_cons] at member
  rcases member with rfl | rfl | rfl | rfl | member
  · change p.elementCount .red < _; omega
  · change p.elementCount .green < _; omega
  · change p.elementCount .blue < _; omega
  · omega
  · obtain ⟨triple,ht,hn⟩ := List.mem_flatMap.mp member
    have referenceBound (color : WireColor) :
        ∀ v ∈ FlatEncoding.referenceFields (triple.reference color), v < p.triples.length+3 := by
      intro v hv
      have atom := (wf triple ht color).trans_le (elementCount_le_triples p degrees color)
      have small := locality triple ht color
      have x := encode_small_int (triple.reference color).offset.1 (by omega)
      have y := encode_small_int (triple.reference color).offset.2 (by omega)
      simp only [FlatEncoding.referenceFields,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega
    simp only [FlatEncoding.tripleFields,List.mem_append] at hn
    rcases hn with (hr | hg) | hb
    · exact referenceBound .red n hr
    · exact referenceBound .green n hg
    · exact referenceBound .blue n hb

end LeanTrominoes.PeriodicThreeDM
