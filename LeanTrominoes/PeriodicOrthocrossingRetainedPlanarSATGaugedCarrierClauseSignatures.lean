/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierClauseOrbits
import LeanTrominoes.PeriodicOrthocrossingCarrierTranslationGeometry

/-!
# Carrier-clause signatures in the gauged periodic planar-SAT drawing

Carrier equality clauses have a rigid residue signature: their perpendicular
coordinate is `6 mod 10`, and their axial coordinate is `4` or `7 mod 10`
according to the implication-clause index.  This module proves that equal
fundamental-domain residues recover the carrier axis, local clause index, and
the first carrier-node position modulo the drawing period.  It also proves
that a raw retained carrier link is uniquely determined by its exact first
node.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

theorem carrierClause_position_and_index
    {Variable : Type*}
    {link : EqualityLink CarrierNode}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {index : Nat}
    (member :
      (clause, index) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx) :
    (index = 0 ∧ clause.position = link.positions.forward) ∨
      (index = 1 ∧
        clause.position = link.positions.backward) := by
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    EmbeddedClause.rename, EmbeddedClause.map] at member
  rcases member with ⟨clauseEq, indexEq⟩ |
      ⟨clauseEq, indexEq⟩
  · exact Or.inl
      ⟨indexEq, congrArg EmbeddedClause.position clauseEq⟩
  · exact Or.inr
      ⟨indexEq, congrArg EmbeddedClause.position clauseEq⟩

theorem carrierClause_position_modTen
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx) :
    if link.first.isHorizontal then
      clause.position.2 % 10 = 6 ∧
        ((clauseIndex = 0 ∧ clause.position.1 % 10 = 4) ∨
          (clauseIndex = 1 ∧ clause.position.1 % 10 = 7))
    else
      clause.position.1 % 10 = 6 ∧
        ((clauseIndex = 0 ∧ clause.position.2 % 10 = 4) ∨
          (clauseIndex = 1 ∧ clause.position.2 % 10 = 7)) := by
  have positionCases :=
    carrierClause_position_and_index clauseMember
  have geometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have direction :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal linkMem
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      (PeriodicCNF.incidenceGraph formula) linkMem
  have common :=
    retainedDrawingCompleteCarrierLinks_common_key
      (PeriodicCNF.incidenceGraph formula) linkMem
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (retainedCarrierNode_indexed_mem
        (PeriodicCNF.incidenceGraph formula) endpoints.1)
  have firstLocal :=
    retainedCarrierNode_localPosition_axis_data
      (PeriodicCNF.incidenceGraph formula)
      endpoints.1 firstAligned
  have axisData :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal endpoints.1 endpoints.2 common
  rw [geometry.positions] at positionCases
  change
    AxisDirection.between
        (link.first.position (PeriodicCNF.incidenceGraph formula))
        (link.second.position (PeriodicCNF.incidenceGraph formula)) =
      (if link.first.isHorizontal then .east else .north)
    at direction
  rw [direction] at positionCases
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal] at positionCases axisData firstLocal ⊢
    have perpendicularResidue :
        (link.first.position
          (PeriodicCNF.incidenceGraph formula)).2 % 10 = 6 := by
      rw [CarrierNode.position_eq_scale_add_local]
      norm_num [Cell.add, Cell.scale, planarMacroScale,
        firstLocal.1, Int.add_emod, Int.mul_emod]
    rcases positionCases with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · exact ⟨by
        rw [positionEq]
        simpa [AxisDirection.placePoint,
          AxisDirection.orientPoint, Cell.add] using perpendicularResidue,
        Or.inl ⟨indexEq, by
          rw [positionEq]
          simp [AxisDirection.placePoint,
            AxisDirection.orientPoint, Cell.add,
            Int.add_emod, axisData.2.1]⟩⟩
    · exact ⟨by
        rw [positionEq]
        simpa [AxisDirection.placePoint,
          AxisDirection.orientPoint, Cell.add] using perpendicularResidue,
        Or.inr ⟨indexEq, by
          rw [positionEq]
          simp [AxisDirection.placePoint,
            AxisDirection.orientPoint, Cell.add,
            Int.add_emod, axisData.2.1]⟩⟩
  · rw [if_neg horizontal] at positionCases axisData firstLocal ⊢
    have perpendicularResidue :
        (link.first.position
          (PeriodicCNF.incidenceGraph formula)).1 % 10 = 6 := by
      rw [CarrierNode.position_eq_scale_add_local]
      norm_num [Cell.add, Cell.scale, planarMacroScale,
        firstLocal.1, Int.add_emod, Int.mul_emod]
    rcases positionCases with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · exact ⟨by
        rw [positionEq]
        simpa [AxisDirection.placePoint,
          AxisDirection.orientPoint, Cell.add] using perpendicularResidue,
        Or.inl ⟨indexEq, by
          rw [positionEq]
          simp [AxisDirection.placePoint,
            AxisDirection.orientPoint, Cell.add,
            Int.add_emod, axisData.2.1]⟩⟩
    · exact ⟨by
        rw [positionEq]
        simpa [AxisDirection.placePoint,
          AxisDirection.orientPoint, Cell.add] using perpendicularResidue,
        Or.inr ⟨indexEq, by
          rw [positionEq]
          simp [AxisDirection.placePoint,
            AxisDirection.orientPoint, Cell.add,
            Int.add_emod, axisData.2.1]⟩⟩

theorem cell_emod_ten_eq_of_planarSATPeriodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : Cell} (shift : Cell)
    (equal :
      first =
        Cell.add second
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift)) :
    first.1 % 10 = second.1 % 10 ∧
      first.2 % 10 = second.2 % 10 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  constructor
  · have coordinateEq := congrArg Prod.fst equal
    simp [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] at coordinateEq
    rw [coordinateEq]
    rw [show
      secondX +
          20 *
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
            shiftX =
        secondX +
          10 *
            (2 *
              (drawingGridSize
                (PeriodicCNF.incidenceGraph formula) : Int) *
              shiftX) by ring,
      Int.add_mul_emod_self_left]
  · have coordinateEq := congrArg Prod.snd equal
    simp [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] at coordinateEq
    rw [coordinateEq]
    rw [show
      secondY +
          20 *
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
            shiftY =
        secondY +
          10 *
            (2 *
              (drawingGridSize
                (PeriodicCNF.incidenceGraph formula) : Int) *
              shiftY) by ring,
      Int.add_mul_emod_self_left]

theorem carrierClause_axis_and_index_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstLinkMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondLinkMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) secondLink).zipIdx)
    (residueEq :
      clauseResidue formula firstClause =
        clauseResidue formula secondClause) :
    firstLink.first.isHorizontal =
        secondLink.first.isHorizontal ∧
      firstIndex = secondIndex := by
  rcases clausePosition_eq_translate_of_residue_eq
      formula residueEq with
    ⟨shift, positionEq⟩
  have coordinateResidues :=
    cell_emod_ten_eq_of_planarSATPeriodTranslate
      formula shift positionEq
  have firstData :=
    carrierClause_position_modTen
      wellFormed degree isLocal firstLinkMem firstMember
  have secondData :=
    carrierClause_position_modTen
      wellFormed degree isLocal secondLinkMem secondMember
  by_cases firstHorizontal :
      firstLink.first.isHorizontal = true
  · rw [if_pos firstHorizontal] at firstData
    by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · rw [if_pos secondHorizontal] at secondData
      refine
        ⟨firstHorizontal.trans secondHorizontal.symm, ?_⟩
      rcases firstData.2 with firstForward | firstBackward <;>
        rcases secondData.2 with secondForward | secondBackward
      · exact firstForward.1.trans secondForward.1.symm
      · exfalso
        have : (4 : Int) = 7 := by
          rw [← firstForward.2, coordinateResidues.1,
            secondBackward.2]
        norm_num at this
      · exfalso
        have : (7 : Int) = 4 := by
          rw [← firstBackward.2, coordinateResidues.1,
            secondForward.2]
        norm_num at this
      · exact firstBackward.1.trans secondBackward.1.symm
    · rw [if_neg secondHorizontal] at secondData
      exfalso
      have : (6 : Int) = 4 ∨ (6 : Int) = 7 := by
        rcases secondData.2 with secondForward | secondBackward
        · exact Or.inl (firstData.1.symm.trans
            (coordinateResidues.2.trans secondForward.2))
        · exact Or.inr (firstData.1.symm.trans
            (coordinateResidues.2.trans secondBackward.2))
      omega
  · rw [if_neg firstHorizontal] at firstData
    by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · rw [if_pos secondHorizontal] at secondData
      exfalso
      have : (6 : Int) = 4 ∨ (6 : Int) = 7 := by
        rcases secondData.2 with secondForward | secondBackward
        · exact Or.inl (firstData.1.symm.trans
            (coordinateResidues.1.trans secondForward.2))
        · exact Or.inr (firstData.1.symm.trans
            (coordinateResidues.1.trans secondBackward.2))
      omega
    · rw [if_neg secondHorizontal] at secondData
      refine
        ⟨Bool.eq_false_iff.mpr firstHorizontal |>.trans
          (Bool.eq_false_iff.mpr secondHorizontal).symm, ?_⟩
      rcases firstData.2 with firstForward | firstBackward <;>
        rcases secondData.2 with secondForward | secondBackward
      · exact firstForward.1.trans secondForward.1.symm
      · exfalso
        have : (4 : Int) = 7 := by
          rw [← firstForward.2, coordinateResidues.2,
            secondBackward.2]
        norm_num at this
      · exfalso
        have : (7 : Int) = 4 := by
          rw [← firstBackward.2, coordinateResidues.2,
            secondForward.2]
        norm_num at this
      · exact firstBackward.1.trans secondBackward.1.symm

def carrierClauseOffset
    (horizontal : Bool) (clauseIndex : Nat) : Cell :=
  if horizontal then
    if clauseIndex = 0 then (3, 0) else (6, 0)
  else
    if clauseIndex = 0 then (0, 3) else (0, 6)

theorem carrierClause_position_eq_first_add_offset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx) :
    clause.position =
      Cell.add
        (link.first.position (PeriodicCNF.incidenceGraph formula))
        (carrierClauseOffset
          link.first.isHorizontal clauseIndex) := by
  have positionCases :=
    carrierClause_position_and_index clauseMember
  have geometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have direction :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal linkMem
  rw [geometry.positions] at positionCases
  change
    AxisDirection.between
        (link.first.position (PeriodicCNF.incidenceGraph formula))
        (link.second.position (PeriodicCNF.incidenceGraph formula)) =
      (if link.first.isHorizontal then .east else .north)
    at direction
  rw [direction] at positionCases
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal] at positionCases
    rcases positionCases with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · simpa [carrierClauseOffset, horizontal,
        indexEq, AxisDirection.placePoint,
        AxisDirection.orientPoint] using positionEq
    · simpa [carrierClauseOffset, horizontal,
        indexEq, AxisDirection.placePoint,
        AxisDirection.orientPoint] using positionEq
  · rw [if_neg horizontal] at positionCases
    rcases positionCases with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · simpa [carrierClauseOffset, horizontal,
        indexEq, AxisDirection.placePoint,
        AxisDirection.orientPoint] using positionEq
    · simpa [carrierClauseOffset, horizontal,
        indexEq, AxisDirection.placePoint,
        AxisDirection.orientPoint] using positionEq

theorem base_eq_translate_of_add_offset_eq
    {firstBase secondBase offset translation : Cell}
    (equal :
      Cell.add firstBase offset =
        Cell.add (Cell.add secondBase offset) translation) :
    firstBase = Cell.add secondBase translation := by
  rcases firstBase with ⟨firstX, firstY⟩
  rcases secondBase with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases translation with ⟨translateX, translateY⟩
  apply Prod.ext
  · have coordinateEq := congrArg Prod.fst equal
    simp [Cell.add] at coordinateEq ⊢
    omega
  · have coordinateEq := congrArg Prod.snd equal
    simp [Cell.add] at coordinateEq ⊢
    omega

theorem carrierFirstPosition_eq_translate_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstLinkMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondLinkMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) secondLink).zipIdx)
    (residueEq :
      clauseResidue formula firstClause =
        clauseResidue formula secondClause) :
    ∃ shift,
      firstLink.first.position (PeriodicCNF.incidenceGraph formula) =
        Cell.add
          (secondLink.first.position
            (PeriodicCNF.incidenceGraph formula))
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift) := by
  have signatureEq :=
    carrierClause_axis_and_index_eq_of_residue_eq
      wellFormed degree isLocal
      firstLinkMem secondLinkMem firstMember secondMember residueEq
  rcases clausePosition_eq_translate_of_residue_eq
      formula residueEq with
    ⟨shift, positionEq⟩
  refine ⟨shift, ?_⟩
  apply base_eq_translate_of_add_offset_eq
  rw [← carrierClause_position_eq_first_add_offset
      wellFormed degree isLocal firstLinkMem firstMember]
  rw [signatureEq.1, signatureEq.2]
  rw [← carrierClause_position_eq_first_add_offset
      wellFormed degree isLocal secondLinkMem secondMember]
  exact positionEq

theorem consecutivePairs_eq_of_fst_eq_of_nodup
    {Value : Type*}
    {values : List Value}
    (nodup : values.Nodup)
    {first second : Value × Value}
    (firstMem : first ∈ consecutivePairs values)
    (secondMem : second ∈ consecutivePairs values)
    (fstEq : first.1 = second.1) :
    first = second := by
  induction values with
  | nil =>
      simp [consecutivePairs] at firstMem
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [consecutivePairs] at firstMem
      | cons next rest =>
          rw [consecutivePairs] at firstMem secondMem
          simp only [List.mem_cons] at firstMem secondMem
          rcases firstMem with firstEq | firstMem <;>
            rcases secondMem with secondEq | secondMem
          · exact firstEq.trans secondEq.symm
          · subst first
            have secondMembers :=
              mem_of_mem_consecutivePairs secondMem
            change head = second.1 at fstEq
            exfalso
            exact (List.nodup_cons.mp nodup).1
              (by
                rw [fstEq]
                exact secondMembers.1)
          · subst second
            have firstMembers :=
              mem_of_mem_consecutivePairs firstMem
            change first.1 = head at fstEq
            exfalso
            exact (List.nodup_cons.mp nodup).1
              (by
                rw [← fstEq]
                exact firstMembers.1)
          · exact induction
              (List.nodup_cons.mp nodup).2
              firstMem secondMem

theorem retainedDrawingCompleteCarrierLinks_eq_of_first_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (firstEq : first.first = second.first) :
    first = second := by
  have firstRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph first).mp firstMem).1
  have secondRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph second).mp secondMem).1
  rcases List.mem_flatMap.mp firstRaw with
    ⟨firstKey, _firstKeyMem, firstChainMem⟩
  rcases List.mem_flatMap.mp secondRaw with
    ⟨secondKey, _secondKeyMem, secondChainMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstChainMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondChainMem
  have keyEq : firstKey = secondKey := by
    rw [← firstCommon.1, ← secondCommon.1, firstEq]
  subst secondKey
  rcases List.mem_map.mp firstChainMem with
    ⟨firstPair, firstPairMem, firstLinkEq⟩
  rcases List.mem_map.mp secondChainMem with
    ⟨secondPair, secondPairMem, secondLinkEq⟩
  have pairEq :
      firstPair = secondPair := by
    apply consecutivePairs_eq_of_fst_eq_of_nodup
      (retainedCompleteCarrierNodes_nodup graph firstKey)
      (List.mem_filter.mp firstPairMem).1
      (List.mem_filter.mp secondPairMem).1
    calc
      firstPair.1 =
          first.first :=
        congrArg EqualityLink.first firstLinkEq
      _ = second.first := firstEq
      _ = secondPair.1 :=
        (congrArg EqualityLink.first secondLinkEq).symm
  subst secondPair
  exact firstLinkEq.symm.trans secondLinkEq

end LeanTrominoes.PeriodicOrthocrossing
