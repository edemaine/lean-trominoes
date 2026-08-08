import LeanTrominoes.PeriodicGraph
import LeanTrominoes.PeriodicThreeDM

/-!
# Incidence graph of periodic three-dimensional matching

This file turns a periodic 3DM presentation into the periodic bipartite graph
used by Theorems 3.7 and 3.8.  Prototype vertices are either indexed triples
or colored elements.  At lattice translate `z`, the incidence belonging to a
reference with offset `d` joins the triple at `z` to its element at `z + d`.

The three edges of every triple are emitted in red, green, blue order.  The
separate incidence tags retain this color information even though the generic
`PeriodicGraph` representation itself is uncolored.
-/

namespace LeanTrominoes

open Gadget

/-- Vertices of the bipartite incidence graph of a periodic 3DM instance. -/
inductive PeriodicThreeDMVertex
  | triple (index : Nat)
  | element (color : WireColor) (atom : Nat)
  deriving DecidableEq, Repr

namespace PeriodicThreeDM

/-- Metadata identifying one colored incidence edge. -/
structure IncidenceTag where
  tripleIndex : Nat
  color : WireColor
  deriving DecidableEq, Repr

/-- Stable red, green, blue order for the incidences of each triple. -/
def incidenceColors : List WireColor :=
  [.red, .green, .blue]

/-- One prototype vertex for every element of a specified color. -/
def coloredElementVertices (problem : PeriodicThreeDM)
    (color : WireColor) : List PeriodicThreeDMVertex :=
  (List.range (problem.elementCount color)).map
    (PeriodicThreeDMVertex.element color)

/-- All colored-element prototype vertices, grouped red, green, blue. -/
def elementVertices (problem : PeriodicThreeDM) :
    List PeriodicThreeDMVertex :=
  problem.coloredElementVertices .red ++
    problem.coloredElementVertices .green ++
    problem.coloredElementVertices .blue

/-- One prototype vertex for every entry of the triple presentation. -/
def tripleVertices (problem : PeriodicThreeDM) :
    List PeriodicThreeDMVertex :=
  (List.range problem.triples.length).map
    PeriodicThreeDMVertex.triple

/-- The three colored incidence tags belonging to one indexed triple. -/
def tripleIncidenceTags (tripleIndex : Nat) : List IncidenceTag :=
  incidenceColors.map fun color => ⟨tripleIndex, color⟩

/-- Every colored incidence tag in triple-presentation order. -/
def incidenceTags (problem : PeriodicThreeDM) : List IncidenceTag :=
  problem.triples.zipIdx.flatMap fun tagged =>
    tripleIncidenceTags tagged.2

/-- The graph edge described by one actual indexed triple and one color. -/
def incidenceEdge (tripleIndex : Nat)
    (triple : PeriodicThreeDMTriple) (color : WireColor) :
    PeriodicEdge PeriodicThreeDMVertex :=
  let reference := triple.reference color
  ⟨.triple tripleIndex, .element color reference.atom, reference.offset⟩

/-- The three colored incidence edges belonging to one indexed triple. -/
def tripleIncidenceEdges (tripleIndex : Nat)
    (triple : PeriodicThreeDMTriple) :
    List (PeriodicEdge PeriodicThreeDMVertex) :=
  incidenceColors.map (incidenceEdge tripleIndex triple)

/-- The graph edge belonging to an incidence tag, with an arbitrary default
triple outside the presentation.  Actual tags always have an in-range index. -/
def incidenceEdgeAt (problem : PeriodicThreeDM)
    (tag : IncidenceTag) : PeriodicEdge PeriodicThreeDMVertex :=
  incidenceEdge tag.tripleIndex
    (problem.triples.getD tag.tripleIndex default) tag.color

/-- The finite periodic bipartite incidence graph of a periodic 3DM problem. -/
def incidenceGraph (problem : PeriodicThreeDM) :
    PeriodicGraph PeriodicThreeDMVertex where
  vertices := problem.tripleVertices ++ problem.elementVertices
  edges := problem.triples.zipIdx.flatMap fun tagged =>
    tripleIncidenceEdges tagged.2 tagged.1

@[simp]
theorem incidenceColors_nodup : incidenceColors.Nodup := by
  decide

/-- Incidence tags can equivalently be enumerated by triple index rather
than by the value/index pairs of `zipIdx`. -/
theorem incidenceTags_eq_range_flatMap (problem : PeriodicThreeDM) :
    problem.incidenceTags =
      (List.range problem.triples.length).flatMap tripleIncidenceTags := by
  unfold incidenceTags
  rw [← List.flatMap_map]
  congr 1
  rw [List.zipIdx_map_snd, List.range_eq_range']

/-- The three colored tags of one triple index are duplicate-free. -/
theorem tripleIncidenceTags_nodup (tripleIndex : Nat) :
    (tripleIncidenceTags tripleIndex).Nodup := by
  apply incidenceColors_nodup.map
  intro first second equality
  cases equality
  rfl

/-- Distinct triple indices contribute disjoint incidence-tag blocks. -/
theorem tripleIncidenceTags_disjoint
    {firstIndex secondIndex : Nat}
    (different : firstIndex ≠ secondIndex) :
    List.Disjoint
      (tripleIncidenceTags firstIndex)
      (tripleIncidenceTags secondIndex) := by
  rw [List.disjoint_left]
  intro tag firstMem secondMem
  simp only [tripleIncidenceTags, List.mem_map] at firstMem secondMem
  rcases firstMem with ⟨firstColor, _, rfl⟩
  rcases secondMem with ⟨secondColor, _, equality⟩
  cases equality
  exact different rfl

/-- Every original incidence edge has one unique tag-list position. -/
theorem incidenceTags_nodup (problem : PeriodicThreeDM) :
    problem.incidenceTags.Nodup := by
  rw [incidenceTags_eq_range_flatMap, List.nodup_flatMap]
  exact
    ⟨fun index _ => tripleIncidenceTags_nodup index,
      List.nodup_range.imp fun different =>
        tripleIncidenceTags_disjoint different⟩

@[simp]
theorem incidenceColors_length : incidenceColors.length = 3 := by
  rfl

theorem coloredElementVertices_nodup (problem : PeriodicThreeDM)
    (color : WireColor) :
    (problem.coloredElementVertices color).Nodup := by
  apply List.nodup_range.map
  intro first second equality
  cases equality
  rfl

theorem coloredElementVertices_mem_iff (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) :
    .element color atom ∈ problem.coloredElementVertices color ↔
      atom < problem.elementCount color := by
  simp [coloredElementVertices]

theorem coloredElementVertices_disjoint (problem : PeriodicThreeDM)
    {first second : WireColor} (different : first ≠ second) :
    List.Disjoint (problem.coloredElementVertices first)
      (problem.coloredElementVertices second) := by
  rw [List.disjoint_left]
  intro vertex firstMem secondMem
  simp only [coloredElementVertices, List.mem_map] at firstMem secondMem
  rcases firstMem with ⟨firstAtom, _, rfl⟩
  rcases secondMem with ⟨secondAtom, _, equality⟩
  cases equality
  exact different rfl

theorem elementVertices_nodup (problem : PeriodicThreeDM) :
    problem.elementVertices.Nodup := by
  rw [elementVertices, List.nodup_append']
  refine ⟨?_, coloredElementVertices_nodup problem .blue, ?_⟩
  · rw [List.nodup_append']
    exact ⟨coloredElementVertices_nodup problem .red,
      coloredElementVertices_nodup problem .green,
      coloredElementVertices_disjoint problem (by decide)⟩
  · rw [List.disjoint_append_left]
    exact ⟨coloredElementVertices_disjoint problem (by decide),
      coloredElementVertices_disjoint problem (by decide)⟩

theorem tripleVertices_nodup (problem : PeriodicThreeDM) :
    problem.tripleVertices.Nodup := by
  apply List.nodup_range.map
  intro first second equality
  cases equality
  rfl

theorem triple_element_vertices_disjoint (problem : PeriodicThreeDM) :
    ∀ triple ∈ problem.tripleVertices,
      ∀ element ∈ problem.elementVertices, triple ≠ element := by
  intro triple tripleMem element elementMem equal
  simp only [tripleVertices, List.mem_map] at tripleMem
  rcases tripleMem with ⟨tripleIndex, _, rfl⟩
  cases element with
  | triple elementIndex =>
      simp [elementVertices, coloredElementVertices] at elementMem
  | element color atom =>
      cases equal

theorem incidenceGraph_vertices_nodup (problem : PeriodicThreeDM) :
    problem.incidenceGraph.vertices.Nodup := by
  change (problem.tripleVertices ++ problem.elementVertices).Nodup
  rw [List.nodup_append]
  exact ⟨tripleVertices_nodup problem, elementVertices_nodup problem,
    triple_element_vertices_disjoint problem⟩

theorem incidenceTag_tripleIndex_lt (problem : PeriodicThreeDM)
    {tag : IncidenceTag} (member : tag ∈ problem.incidenceTags) :
    tag.tripleIndex < problem.triples.length := by
  simp only [incidenceTags, List.mem_flatMap] at member
  rcases member with ⟨taggedTriple, taggedMem, tagMem⟩
  simp only [tripleIncidenceTags, List.mem_map] at tagMem
  rcases tagMem with ⟨color, colorMem, rfl⟩
  exact List.snd_lt_of_mem_zipIdx taggedMem

theorem incidenceEdgeAt_eq_of_tag_mem (problem : PeriodicThreeDM)
    {tag : IncidenceTag} (member : tag ∈ problem.incidenceTags) :
    problem.incidenceEdgeAt tag =
      incidenceEdge tag.tripleIndex
        (problem.triples[tag.tripleIndex]'(incidenceTag_tripleIndex_lt
          problem member)) tag.color := by
  unfold incidenceEdgeAt
  rw [List.getD_eq_getElem]

/-- The uncolored graph edge list and the colored tag list have exactly the
same order.  This lets later drawing routes recover their wire colors by
using the same list index. -/
theorem incidenceGraph_edges_eq_tags_map
    (problem : PeriodicThreeDM) :
    problem.incidenceGraph.edges =
      problem.incidenceTags.map problem.incidenceEdgeAt := by
  change
    problem.triples.zipIdx.flatMap
        (fun tagged =>
          tripleIncidenceEdges tagged.2 tagged.1) =
      (problem.triples.zipIdx.flatMap fun tagged =>
        tripleIncidenceTags tagged.2).map problem.incidenceEdgeAt
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro tagged taggedMem
  simp only [tripleIncidenceEdges, tripleIncidenceTags, List.map_map]
  apply List.map_congr_left
  intro color colorMem
  change incidenceEdge tagged.2 tagged.1 color =
    incidenceEdge tagged.2
      (problem.triples.getD tagged.2 default) color
  have indexLt : tagged.2 < problem.triples.length :=
    List.snd_lt_of_mem_zipIdx taggedMem
  rw [List.getD_eq_getElem _ _ indexLt]
  have tripleAt :
      problem.triples[tagged.2]'indexLt = tagged.1 := by
    simpa using (List.mem_zipIdx' taggedMem).2.symm
  rw [tripleAt]

@[simp]
theorem incidenceGraph_edges_length (problem : PeriodicThreeDM) :
    problem.incidenceGraph.edges.length =
      problem.incidenceTags.length := by
  rw [incidenceGraph_edges_eq_tags_map]
  simp

/-- A generated incidence edge joins precisely the translated triple and
translated colored element described by its reference. -/
theorem incidenceEdge_connects
    (tripleIndex : Nat) (triple : PeriodicThreeDMTriple)
    (color : WireColor) (translate : Cell) :
    (incidenceEdge tripleIndex triple color).Connects
      (.triple tripleIndex, translate)
      (.element color (triple.reference color).atom,
        Cell.add translate (triple.reference color).offset) := by
  apply Or.inl
  exact ⟨translate, rfl, rfl⟩

theorem incidenceGraph_isWellFormed (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) :
    problem.incidenceGraph.IsWellFormed := by
  constructor
  · exact incidenceGraph_vertices_nodup problem
  · intro edge edgeMem
    simp only [incidenceGraph, List.mem_flatMap] at edgeMem
    rcases edgeMem with ⟨taggedTriple, taggedMem, edgeMem⟩
    simp only [tripleIncidenceEdges, List.mem_map] at edgeMem
    rcases edgeMem with ⟨color, colorMem, rfl⟩
    let tripleIndex := taggedTriple.2
    let triple := taggedTriple.1
    have indexLt : tripleIndex < problem.triples.length :=
      List.snd_lt_of_mem_zipIdx taggedMem
    have tripleMem : triple ∈ problem.triples :=
      List.fst_mem_of_mem_zipIdx taggedMem
    have referenceLt :=
      wellFormed triple tripleMem color
    simp only [incidenceEdge]
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨tripleIndex, List.mem_range.mpr indexLt, rfl⟩
    · apply List.mem_append_right
      cases color with
      | red =>
          apply List.mem_append_left
          apply List.mem_append_left
          exact
            (coloredElementVertices_mem_iff problem .red
              (triple.reference .red).atom).2 referenceLt
      | green =>
          apply List.mem_append_left
          apply List.mem_append_right
          exact
            (coloredElementVertices_mem_iff problem .green
              (triple.reference .green).atom).2 referenceLt
      | blue =>
          apply List.mem_append_right
          exact
            (coloredElementVertices_mem_iff problem .blue
              (triple.reference .blue).atom).2 referenceLt

private theorem filterMap_reference_length_eq_count
    (triples : List PeriodicThreeDMTriple)
    (color : WireColor) (atom : Nat) :
    ((List.range triples.length).filterMap fun tripleIndex =>
      let reference :=
        (triples.getD tripleIndex default).reference color
      if reference.atom = atom then
        some (Incidence.mk tripleIndex reference.offset)
      else
        none).length =
      (triples.map fun triple =>
        (triple.reference color).atom).count atom := by
  induction triples using List.reverseRec with
  | nil => simp
  | append_singleton triples triple induction =>
      have prefixEquality :
          (List.range triples.length).filterMap
              (fun tripleIndex =>
                let reference :=
                  ((triples ++ [triple]).getD tripleIndex default).reference
                    color
                if reference.atom = atom then
                  some (Incidence.mk tripleIndex reference.offset)
                else none) =
            (List.range triples.length).filterMap
              (fun tripleIndex =>
                let reference :=
                  (triples.getD tripleIndex default).reference color
                if reference.atom = atom then
                  some (Incidence.mk tripleIndex reference.offset)
                else none) := by
        apply List.filterMap_congr
        intro tripleIndex indexMem
        rw [List.getD_append]
        exact List.mem_range.mp indexMem
      have lastLookup :
          (triples ++ [triple]).getD triples.length default = triple := by
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp
      rw [List.length_append, List.length_singleton, List.range_succ,
        List.filterMap_append, List.length_append]
      rw [prefixEquality, induction]
      simp only [List.map_append, List.map_singleton,
        List.count_append, List.count_singleton]
      simp only [List.filterMap_cons, List.filterMap_nil]
      rw [lastLookup]
      by_cases same : (triple.reference color).atom = atom
      · simp [same]
      · simp [same]

theorem degree_eq_reference_count (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) :
    problem.degree color atom =
      (problem.triples.map fun triple =>
        (triple.reference color).atom).count atom := by
  exact filterMap_reference_length_eq_count
    problem.triples color atom

theorem tripleIncidenceEdges_element_count
    (tripleIndex : Nat) (triple : PeriodicThreeDMTriple)
    (color : WireColor) (atom : Nat) :
    ((tripleIncidenceEdges tripleIndex triple).flatMap
        PeriodicEdge.incidences).count (.element color atom) =
      if (triple.reference color).atom = atom then 1 else 0 := by
  cases color with
  | red =>
      by_cases same : (triple.reference .red).atom = atom
      · subst atom
        simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences]
      · simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences, same]
  | green =>
      by_cases same : (triple.reference .green).atom = atom
      · subst atom
        simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences]
      · simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences, same]
  | blue =>
      by_cases same : (triple.reference .blue).atom = atom
      · subst atom
        simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences]
      · simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
          PeriodicEdge.incidences, same]

theorem taggedIncidenceEdges_element_count
    (taggedTriples : List (PeriodicThreeDMTriple × Nat))
    (color : WireColor) (atom : Nat) :
    (taggedTriples.flatMap (fun tagged =>
        tripleIncidenceEdges tagged.2 tagged.1) |>.flatMap
          PeriodicEdge.incidences).count (.element color atom) =
      (taggedTriples.map fun tagged =>
        (tagged.1.reference color).atom).count atom := by
  induction taggedTriples with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.flatMap_cons, List.flatMap_append,
        List.count_append, List.map_cons, List.count_cons]
      rw [tripleIncidenceEdges_element_count, induction]
      by_cases same : (tagged.1.reference color).atom = atom
      · simp [same, Nat.add_comm]
      · simp [same]

/-- The ordinary graph degree of a colored-element vertex is exactly its
periodic-3DM incidence degree. -/
theorem incidenceGraph_element_degree (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) :
    problem.incidenceGraph.incidences.count (.element color atom) =
      problem.degree color atom := by
  rw [show problem.incidenceGraph.incidences =
    (problem.triples.zipIdx.flatMap fun tagged =>
      tripleIncidenceEdges tagged.2 tagged.1).flatMap
        PeriodicEdge.incidences by rfl]
  rw [taggedIncidenceEdges_element_count]
  have mapEquality :
      problem.triples.zipIdx.map
          (fun tagged => (tagged.1.reference color).atom) =
        problem.triples.map
          (fun triple => (triple.reference color).atom) := by
    calc
      _ = (problem.triples.zipIdx.map Prod.fst).map
          (fun triple => (triple.reference color).atom) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro tagged taggedMem
            rfl
      _ = _ := by rw [List.zipIdx_map_fst]
  rw [mapEquality]
  exact (degree_eq_reference_count problem color atom).symm

theorem tripleIncidenceEdges_triple_count
    (tripleIndex : Nat) (triple : PeriodicThreeDMTriple)
    (wantedIndex : Nat) :
    ((tripleIncidenceEdges tripleIndex triple).flatMap
        PeriodicEdge.incidences).count (.triple wantedIndex) =
      if tripleIndex = wantedIndex then 3 else 0 := by
  by_cases same : tripleIndex = wantedIndex
  · subst wantedIndex
    simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
      PeriodicEdge.incidences]
  · simp [tripleIncidenceEdges, incidenceColors, incidenceEdge,
      PeriodicEdge.incidences, same]

theorem taggedIncidenceEdges_triple_count
    (taggedTriples : List (PeriodicThreeDMTriple × Nat))
    (wantedIndex : Nat) :
    (taggedTriples.flatMap (fun tagged =>
        tripleIncidenceEdges tagged.2 tagged.1) |>.flatMap
          PeriodicEdge.incidences).count (.triple wantedIndex) =
      (taggedTriples.map fun tagged =>
        if tagged.2 = wantedIndex then 3 else 0).sum := by
  induction taggedTriples with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.flatMap_cons, List.flatMap_append,
        List.count_append, List.map_cons, List.sum_cons]
      rw [tripleIncidenceEdges_triple_count, induction]

private theorem tripleWeight_sum_eq_zero_of_not_mem
    (taggedTriples : List (PeriodicThreeDMTriple × Nat))
    (wantedIndex : Nat)
    (absent : wantedIndex ∉ taggedTriples.map Prod.snd) :
    (taggedTriples.map fun tagged =>
      if tagged.2 = wantedIndex then 3 else 0).sum = 0 := by
  induction taggedTriples with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      have different : tagged.2 ≠ wantedIndex := by
        intro equal
        exact absent.1 equal.symm
      simp [different, induction absent.2]

private theorem tripleWeight_sum_le_three_of_nodup
    (taggedTriples : List (PeriodicThreeDMTriple × Nat))
    (wantedIndex : Nat)
    (indicesNodup : (taggedTriples.map Prod.snd).Nodup) :
    (taggedTriples.map fun tagged =>
      if tagged.2 = wantedIndex then 3 else 0).sum ≤ 3 := by
  induction taggedTriples with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.map_cons] at indicesNodup
      rw [List.nodup_cons] at indicesNodup
      by_cases same : tagged.2 = wantedIndex
      · have absent : wantedIndex ∉ rest.map Prod.snd := by
          rw [← same]
          exact indicesNodup.1
        simp only [List.map_cons, List.sum_cons, if_pos same]
        rw [tripleWeight_sum_eq_zero_of_not_mem
          rest wantedIndex absent]
      · simp only [List.map_cons, List.sum_cons, if_neg same, zero_add]
        exact induction indicesNodup.2

/-- Every indexed triple vertex has its expected graph-theoretic degree
three; arbitrary indices not in the presentation have degree zero. -/
theorem incidenceGraph_triple_degree_le_three
    (problem : PeriodicThreeDM) (tripleIndex : Nat) :
    problem.incidenceGraph.incidences.count (.triple tripleIndex) ≤ 3 := by
  rw [show problem.incidenceGraph.incidences =
    (problem.triples.zipIdx.flatMap fun tagged =>
      tripleIncidenceEdges tagged.2 tagged.1).flatMap
        PeriodicEdge.incidences by rfl]
  rw [taggedIncidenceEdges_triple_count]
  exact tripleWeight_sum_le_three_of_nodup
    problem.triples.zipIdx tripleIndex
    (List.nodup_zipIdx_map_snd problem.triples)

theorem degree_eq_zero_of_not_lt (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (color : WireColor) (atom : Nat)
    (notInRange : ¬atom < problem.elementCount color) :
    problem.degree color atom = 0 := by
  rw [degree_eq_reference_count]
  apply List.count_eq_zero_of_not_mem
  intro atomMem
  rcases List.mem_map.mp atomMem with
    ⟨triple, tripleMem, atomEqual⟩
  have referenceLt := wellFormed triple tripleMem color
  rw [atomEqual] at referenceLt
  exact notInRange referenceLt

/-- Well-formed degree-two-or-three 3DM presentations produce ordinary
periodic incidence graphs of maximum degree three. -/
theorem incidenceGraph_degreeAtMostThree
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degreeBound : problem.DegreeTwoOrThree) :
    problem.incidenceGraph.DegreeAtMost 3 := by
  intro vertex
  cases vertex with
  | triple tripleIndex =>
      exact incidenceGraph_triple_degree_le_three problem tripleIndex
  | element color atom =>
      rw [incidenceGraph_element_degree]
      by_cases inRange : atom < problem.elementCount color
      · have bounded := degreeBound color atom inRange
        simp at bounded
        omega
      · rw [degree_eq_zero_of_not_lt
          problem wellFormed color atom inRange]
        omega

end PeriodicThreeDM
end LeanTrominoes
