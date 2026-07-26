import LeanTrominoes.PeriodicThreeDMContractionDrawing
import LeanTrominoes.PeriodicThreeDMContractionOrientation

/-!
# Incidence coverage by contracted periodic 3DM edges

The executable contracted graph groups edges by colored element, whereas the
original incidence graph groups them by triple.  This file proves that,
under the well-formed degree-two-or-three promise, flattening the original
incidence tags stored by all contracted edges covers exactly the original
incidence-tag list.

The local statement is stronger and computational: for each colored element,
flattening its emitted edges' metadata is literally the map of that element's
incidence list to tags.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Original incidence tags represented by all executable contracted edges,
in contracted-edge order. -/
def contractedIncidenceTags (problem : PeriodicThreeDM) :
    List IncidenceTag :=
  problem.contractedEdges.flatMap ContractedEdge.incidenceTags

/-- Incidence tags grouped first by color and then by their colored
element, rather than by triple. -/
def incidenceTagsByElement (problem : PeriodicThreeDM) :
    List IncidenceTag :=
  incidenceColors.flatMap fun color =>
    (List.range (problem.elementCount color)).flatMap fun atom =>
      (problem.incidences color atom).map fun incidence =>
        (⟨incidence.tripleIndex, color⟩ : IncidenceTag)

/-- On a degree-two-or-three colored element, flattening the tags stored by
its emitted edges recovers exactly its original incidence list. -/
theorem contractedEdgesForElement_incidenceTags
    (problem : PeriodicThreeDM)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color) :
    (problem.contractedEdgesForElement color atom).flatMap
        ContractedEdge.incidenceTags =
      (problem.incidences color atom).map fun incidence =>
        (⟨incidence.tripleIndex, color⟩ : IncidenceTag) := by
  have degree := degreeTwoOrThree color atom atomLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at degree
  unfold PeriodicThreeDM.degree at degree
  unfold contractedEdgesForElement
  generalize incidencesEq :
      problem.incidences color atom = incidences at degree ⊢
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨third, incidences⟩
  · rfl
  rcases incidences with _ | ⟨fourth, incidences⟩
  · rfl
  simp at degree

/-- Reordering the original incidence tags by colored element introduces no
duplicates.  This is the uniqueness invariant needed to trace each segment
of a contracted route back to one original incidence route. -/
theorem incidenceTagsByElement_nodup
    (problem : PeriodicThreeDM) :
    problem.incidenceTagsByElement.Nodup := by
  rw [incidenceTagsByElement, List.nodup_flatMap]
  constructor
  · intro color colorMem
    rw [List.nodup_flatMap]
    constructor
    · intro atom atomMem
      apply List.Nodup.map_on
      · intro first firstMem second secondMem tagEq
        have firstReference :=
          reference_eq_of_incidence_mem
            problem color atom firstMem
        have secondReference :=
          reference_eq_of_incidence_mem
            problem color atom secondMem
        have indexEq : first.tripleIndex = second.tripleIndex := by
          exact congrArg IncidenceTag.tripleIndex tagEq
        cases first with
        | mk firstIndex firstOffset =>
          cases second with
          | mk secondIndex secondOffset =>
            simp only at indexEq firstReference secondReference ⊢
            subst secondIndex
            have offsetEq : firstOffset = secondOffset :=
              firstReference.2.symm.trans secondReference.2
            cases offsetEq
            rfl
      · unfold incidences
        apply List.Nodup.filterMap
        · intro first second incidence firstMem secondMem
          simp only [Option.mem_def] at firstMem secondMem
          split at firstMem
          next =>
            simp only [Option.some.injEq] at firstMem
            split at secondMem
            next =>
              simp only [Option.some.injEq] at secondMem
              subst incidence
              injections
              omega
            next => simp at secondMem
          next => simp at firstMem
        · exact List.nodup_range
    · apply List.nodup_range.pairwise_of_forall_ne
      intro firstAtom firstAtomMem secondAtom secondAtomMem different
      unfold Function.onFun
      rw [List.disjoint_left]
      intro tag firstMem secondMem
      simp only [List.mem_map] at firstMem secondMem
      rcases firstMem with
        ⟨firstIncidence, firstIncidenceMem, rfl⟩
      rcases secondMem with
        ⟨secondIncidence, secondIncidenceMem, tagEq⟩
      have firstReference :=
        reference_eq_of_incidence_mem
          problem color firstAtom firstIncidenceMem
      have secondReference :=
        reference_eq_of_incidence_mem
          problem color secondAtom secondIncidenceMem
      have tripleIndexEq :
          firstIncidence.tripleIndex =
            secondIncidence.tripleIndex :=
        (congrArg IncidenceTag.tripleIndex tagEq).symm
      have atomEq :
          firstAtom = secondAtom := by
        rw [tripleIndexEq] at firstReference
        exact firstReference.1.symm.trans secondReference.1
      exact different atomEq
  · apply incidenceColors_nodup.pairwise_of_forall_ne
    intro firstColor firstColorMem secondColor secondColorMem different
    unfold Function.onFun
    rw [List.disjoint_left]
    intro tag firstMem secondMem
    simp only [List.mem_flatMap, List.mem_map] at firstMem secondMem
    rcases firstMem with
      ⟨firstAtom, firstAtomMem, first, firstIncidenceMem, rfl⟩
    rcases secondMem with
      ⟨secondAtom, secondAtomMem, second, secondIncidenceMem, tagEq⟩
    have colorEq :
        firstColor = secondColor :=
      (congrArg IncidenceTag.color tagEq).symm
    exact different colorEq

/-- Under the degree promise, executable contracted-edge metadata is
definitionally the same element-major incidence enumeration. -/
theorem contractedIncidenceTags_eq_byElement
    (problem : PeriodicThreeDM)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    problem.contractedIncidenceTags =
      problem.incidenceTagsByElement := by
  unfold contractedIncidenceTags contractedEdges incidenceTagsByElement
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro color colorMem
  unfold contractedEdgesForColor
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro atom atomMem
  exact contractedEdgesForElement_incidenceTags
    problem degreeTwoOrThree color atom
      (List.mem_range.mp atomMem)

/-- No original incidence route is represented twice by the executable
contracted graph. -/
theorem contractedIncidenceTags_nodup
    (problem : PeriodicThreeDM)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    problem.contractedIncidenceTags.Nodup := by
  rw [contractedIncidenceTags_eq_byElement
    problem degreeTwoOrThree]
  exact incidenceTagsByElement_nodup problem

/-- Any original tag stored by an emitted contracted edge is a genuine tag
of the original incidence graph. -/
theorem incidenceTag_mem_of_contractedEdge
    (problem : PeriodicThreeDM)
    {edge : ContractedEdge}
    (edgeMem : edge ∈ problem.contractedEdges)
    {tag : IncidenceTag}
    (tagMem : tag ∈ edge.incidenceTags) :
    tag ∈ problem.incidenceTags := by
  simp only [contractedEdges, List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨color, colorMem, edgeMem⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom edgeMem
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.incidenceTags,
        List.mem_singleton] at tagMem
      subst tag
      have metadata :=
        contractedEdgesForElement_metadata
          problem color atom edgeMem
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      exact incidenceTag_mem_of_incidence_mem
        problem edgeColor edgeAtom incidenceMembers.1
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.incidenceTags,
        ContractedEdge.sourceTag, ContractedEdge.targetTag,
        List.mem_cons, List.not_mem_nil, or_false] at tagMem
      have metadata :=
        contractedEdgesForElement_metadata
          problem color atom edgeMem
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      rcases tagMem with rfl | rfl
      · exact incidenceTag_mem_of_incidence_mem
          problem edgeColor edgeAtom incidenceMembers.1
      · exact incidenceTag_mem_of_incidence_mem
          problem edgeColor edgeAtom incidenceMembers.2.1

/-- Every tag in the flattened contracted metadata is an original incidence
tag.  This direction does not need either structural promise. -/
theorem contractedIncidenceTag_mem_original
    (problem : PeriodicThreeDM)
    {tag : IncidenceTag}
    (member : tag ∈ problem.contractedIncidenceTags) :
    tag ∈ problem.incidenceTags := by
  simp only [contractedIncidenceTags, List.mem_flatMap] at member
  rcases member with ⟨edge, edgeMem, tagMem⟩
  exact incidenceTag_mem_of_contractedEdge
    problem edgeMem tagMem

/-- The incidence record generated by an in-range tag belongs to the
colored element named by that tag's actual triple reference. -/
theorem incidence_of_tag_mem
    (problem : PeriodicThreeDM)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    let triple :=
      problem.triples[tag.tripleIndex]'(
        incidenceTag_tripleIndex_lt problem member)
    let reference := triple.reference tag.color
    (⟨tag.tripleIndex, reference.offset⟩ : Incidence) ∈
      problem.incidences tag.color reference.atom := by
  let indexLt := incidenceTag_tripleIndex_lt problem member
  let triple := problem.triples[tag.tripleIndex]'indexLt
  let reference := triple.reference tag.color
  simp only [incidences, List.mem_filterMap]
  refine
    ⟨tag.tripleIndex, List.mem_range.mpr indexLt, ?_⟩
  rw [List.getD_eq_getElem _ _ indexLt]
  simp

/-- Every original incidence tag is represented by one of the executable
contracted edges under the well-formed degree promise. -/
theorem originalIncidenceTag_mem_contracted
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    tag ∈ problem.contractedIncidenceTags := by
  let indexLt := incidenceTag_tripleIndex_lt problem member
  let triple := problem.triples[tag.tripleIndex]'indexLt
  let reference := triple.reference tag.color
  let incidence : Incidence :=
    ⟨tag.tripleIndex, reference.offset⟩
  have tripleMem : triple ∈ problem.triples :=
    List.getElem_mem indexLt
  have atomLt :
      reference.atom < problem.elementCount tag.color :=
    wellFormed triple tripleMem tag.color
  have incidenceMem :
      incidence ∈
        problem.incidences tag.color reference.atom := by
    simpa [triple, reference, incidence, indexLt] using
      incidence_of_tag_mem problem member
  have localTagMem :
      tag ∈
        (problem.contractedEdgesForElement
          tag.color reference.atom).flatMap
            ContractedEdge.incidenceTags := by
    rw [contractedEdgesForElement_incidenceTags
      problem degreeTwoOrThree tag.color reference.atom atomLt]
    apply List.mem_map.mpr
    refine ⟨incidence, incidenceMem, ?_⟩
    cases tag
    rfl
  rcases List.mem_flatMap.mp localTagMem with
    ⟨edge, edgeLocalMem, tagEdgeMem⟩
  apply List.mem_flatMap.mpr
  refine ⟨edge, ?_, tagEdgeMem⟩
  unfold contractedEdges
  apply List.mem_flatMap.mpr
  refine ⟨tag.color, ?_, ?_⟩
  · cases tag.color <;> simp [incidenceColors]
  unfold contractedEdgesForColor
  apply List.mem_flatMap.mpr
  exact
    ⟨reference.atom, List.mem_range.mpr atomLt,
      edgeLocalMem⟩

/-- Flattened contracted-edge metadata and the original incidence graph
contain exactly the same tags. -/
theorem contractedIncidenceTag_mem_iff
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    (tag : IncidenceTag) :
    tag ∈ problem.contractedIncidenceTags ↔
      tag ∈ problem.incidenceTags := by
  exact
    ⟨contractedIncidenceTag_mem_original problem,
      originalIncidenceTag_mem_contracted
        problem wellFormed degreeTwoOrThree⟩

/-- Contracted-edge metadata is a permutation, not merely a setwise cover,
of the original incidence routes.  Thus every original route is consumed
exactly once by contraction. -/
theorem contractedIncidenceTags_perm
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    problem.contractedIncidenceTags.Perm
      problem.incidenceTags := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    (contractedIncidenceTags_nodup
      problem degreeTwoOrThree)
    (incidenceTags_nodup problem)
  apply Finset.ext
  intro tag
  simp only [List.mem_toFinset]
  exact contractedIncidenceTag_mem_iff
    problem wellFormed degreeTwoOrThree tag

/-- The local endpoint-opposition law applies to every edge in the complete
executable contracted graph. -/
theorem contractedEdge_endpointInward_ne
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {edge : ContractedEdge}
    (edgeMem : edge ∈ problem.contractedEdges)
    (sourceCell : Cell) :
    edge.sourceInward values sourceCell ≠
      edge.targetInward values sourceCell := by
  simp only [contractedEdges, List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨color, colorMem, edgeMem⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
  exact contractedEdge_endpointInward_ne_of_mem
    problem values valid color atom
      (List.mem_range.mp atomMem) edgeMem sourceCell

end PeriodicThreeDM
end LeanTrominoes
