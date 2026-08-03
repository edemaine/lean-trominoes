import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder
import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes
import Mathlib.Data.List.Sort

/-!
# Clockwise ordering of positioned clause literals

A planar clause replacement has fixed boundary ports, while an arbitrary
orthogonal source drawing can leave a clause in any cyclic rotation.  This
file sorts each positioned clause's *tagged* literals by the clockwise rank
of their source-route first directions.  The tags retain the original
literal indices, so the same geometric routes can be reused after sorting.

Only presentation order changes: clause positions, literals, and Boolean
semantics are all preserved up to permutation.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Three distinct genuine directions whose ranks are nondecreasing occur
in clockwise order without requiring a cyclic rotation. -/
theorem inClockwiseOrder_of_rank_le
    {first second third : AxisDirection}
    (firstGenuine : first.IsGenuine)
    (secondGenuine : second.IsGenuine)
    (thirdGenuine : third.IsGenuine)
    (firstSecond : first ≠ second)
    (firstThird : first ≠ third)
    (secondThird : second ≠ third)
    (firstLeSecond : first.clockwiseRank ≤ second.clockwiseRank)
    (secondLeThird : second.clockwiseRank ≤ third.clockwiseRank) :
    InClockwiseOrder first second third := by
  native_decide +revert

end AxisDirection

namespace PositionedPeriodicCNF

variable {Variable : Type*}

/-- First-direction rank attached to one original tagged literal. -/
def clauseLiteralDirectionRank
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (taggedLiteral : PeriodicLiteral Variable × Nat) : Nat :=
  (AxisDirection.polylineFirstDirection
    (routes clauseIndex taggedLiteral.2)).clockwiseRank

/-- Stable comparison used to put original literal tags clockwise. -/
def clauseLiteralDirectionLE
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (first second : PeriodicLiteral Variable × Nat) : Prop :=
  clauseLiteralDirectionRank routes clauseIndex first ≤
    clauseLiteralDirectionRank routes clauseIndex second

instance clauseLiteralDirectionLE_decidable
    (routes : IncidenceRoutes) (clauseIndex : Nat) :
    DecidableRel
      (clauseLiteralDirectionLE (Variable := Variable)
        routes clauseIndex) := by
  intro first second
  unfold clauseLiteralDirectionLE
  infer_instance

/-- Original literal tags, stably sorted by clockwise first-direction rank. -/
def clauseLiteralOrder
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    List (PeriodicLiteral Variable × Nat) :=
  clause.literals.zipIdx.insertionSort
    (clauseLiteralDirectionLE routes clauseIndex)

/-- Reorder one positioned clause while retaining its drawing position. -/
def orderClauseByRouteDirection
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause Variable where
  position := clause.position
  literals := (clauseLiteralOrder routes clauseIndex clause).map Prod.fst

/-- Reorder every clause's literals by the clockwise order of its routes. -/
def orderClausesByRouteDirection
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : PositionedPeriodicCNF Variable where
  clauses := source.clauses.zipIdx.map fun taggedClause =>
    orderClauseByRouteDirection routes taggedClause.2 taggedClause.1

/-- Reindex the unchanged source routes through the sorted literal lists. -/
def orderRoutesByClauseDirection
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match (clauseLiteralOrder routes clauseIndex clause)[literalIndex]? with
        | none => []
        | some taggedLiteral => routes clauseIndex taggedLiteral.2

/-- Reindex a canonical source route and translate it between the old and
new clause-anchor gauges.  The translation is by a whole number of drawing
periods, so this changes only the selected representative of the periodic
route orbit. -/
def orderCanonicalRoutesByClauseDirection
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some sourceClause =>
        let orderedClause :=
          orderClauseByRouteDirection routes clauseIndex sourceClause
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor sourceClause.literals)
              (PeriodicCNF.clauseAnchor orderedClause.literals)))
          (orderRoutesByClauseDirection source routes
            clauseIndex literalIndex)

@[simp]
theorem orderClauseByRouteDirection_position
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    (orderClauseByRouteDirection routes clauseIndex clause).position =
      clause.position := by
  rfl

/-- Sorting retains precisely the original tagged literals. -/
theorem clauseLiteralOrder_perm
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    (clauseLiteralOrder routes clauseIndex clause).Perm
      clause.literals.zipIdx := by
  exact List.perm_insertionSort
    (clauseLiteralDirectionLE routes clauseIndex) clause.literals.zipIdx

/-- The selected original tags are nondecreasing in clockwise rank. -/
theorem clauseLiteralOrder_pairwise
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    (clauseLiteralOrder routes clauseIndex clause).Pairwise
      (clauseLiteralDirectionLE routes clauseIndex) := by
  letI : Std.Total
      (clauseLiteralDirectionLE
        (Variable := Variable) routes clauseIndex) :=
    ⟨fun first second => by
      unfold clauseLiteralDirectionLE
      exact le_total _ _⟩
  letI : IsTrans _
      (clauseLiteralDirectionLE
        (Variable := Variable) routes clauseIndex) :=
    ⟨fun first second third firstSecond secondThird => by
      unfold clauseLiteralDirectionLE at firstSecond secondThird ⊢
      exact firstSecond.trans secondThird⟩
  exact List.pairwise_insertionSort _ _

/-- Reordering retains precisely the original untagged literals. -/
theorem orderClauseByRouteDirection_literals_perm
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    (orderClauseByRouteDirection routes clauseIndex clause).literals.Perm
      clause.literals := by
  simpa [orderClauseByRouteDirection] using
    (clauseLiteralOrder_perm routes clauseIndex clause).map Prod.fst

/-- A reordered clause has the same width as its source clause. -/
@[simp]
theorem orderClauseByRouteDirection_length
    (routes : IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    (orderClauseByRouteDirection routes clauseIndex clause).literals.length =
      clause.literals.length :=
  (orderClauseByRouteDirection_literals_perm
    routes clauseIndex clause).length_eq

/-- Clause membership is transported forward through the ordering map. -/
theorem orderClauseByRouteDirection_mem
    {source : PositionedPeriodicCNF Variable}
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    (orderClauseByRouteDirection routes clauseIndex clause, clauseIndex) ∈
      (orderClausesByRouteDirection source routes).clauses.zipIdx := by
  have sourceLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp clauseMember
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp [orderClausesByRouteDirection, List.getElem?_map,
    List.getElem?_zipIdx, sourceLookup]

/-- Every reordered clause recovers the unique source clause at its index. -/
theorem exists_sourceClause_of_orderedClause_mem
    {source : PositionedPeriodicCNF Variable}
    (routes : IncidenceRoutes)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx) :
    ∃ sourceClause,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      orderedClause =
        orderClauseByRouteDirection routes clauseIndex sourceClause := by
  have orderedLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp clauseMember
  cases sourceLookup : source.clauses[clauseIndex]? with
  | none =>
      simp [orderClausesByRouteDirection, List.getElem?_map,
        List.getElem?_zipIdx, sourceLookup] at orderedLookup
  | some sourceClause =>
      refine ⟨sourceClause,
        List.mk_mem_zipIdx_iff_getElem?.mpr sourceLookup, ?_⟩
      simpa [orderClausesByRouteDirection, List.getElem?_map,
        List.getElem?_zipIdx, sourceLookup] using orderedLookup.symm

/-- A genuine reordered incidence recovers its original literal tag and
therefore looks up exactly the unchanged original route. -/
theorem exists_sourceLiteral_of_orderedLiteral_mem
    {source : PositionedPeriodicCNF Variable}
    (routes : IncidenceRoutes)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral sourceLiteralIndex,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx ∧
      orderedClause =
        orderClauseByRouteDirection routes clauseIndex sourceClause ∧
      literal = sourceLiteral ∧
      orderRoutesByClauseDirection source routes
          clauseIndex literalIndex =
        routes clauseIndex sourceLiteralIndex := by
  rcases exists_sourceClause_of_orderedClause_mem routes clauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have literalLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp literalMember
  rw [orderedClauseEq, orderClauseByRouteDirection,
    List.getElem?_map, Option.map_eq_some_iff] at literalLookup
  rcases literalLookup with
    ⟨taggedLiteral, taggedLookup, taggedLiteralEq⟩
  have taggedMember :
      taggedLiteral ∈
        clauseLiteralOrder routes clauseIndex sourceClause :=
    List.mem_iff_getElem?.mpr ⟨literalIndex, taggedLookup⟩
  have sourceLiteralMember :
      taggedLiteral ∈ sourceClause.literals.zipIdx :=
    (clauseLiteralOrder_perm
      routes clauseIndex sourceClause).mem_iff.mp taggedMember
  refine ⟨sourceClause, taggedLiteral.1, taggedLiteral.2,
    sourceClauseMember, sourceLiteralMember, orderedClauseEq,
    taggedLiteralEq.symm, ?_⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  simp [orderRoutesByClauseDirection, sourceClauseLookup, taggedLookup]

/-- Anchor-gauged reordering preserves the canonical endpoints and
orthogonality of every genuine incidence. -/
theorem orderCanonicalRoutesByClauseDirection_valid
    [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (family : CanonicalOrthogonalIncidenceRoutes source placement)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source family.routes).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    (orderCanonicalRoutesByClauseDirection
        source placement family.routes clauseIndex literalIndex).head? =
        some (canonicalClausePosition placement orderedClause) ∧
      (orderCanonicalRoutesByClauseDirection
        source placement family.routes clauseIndex literalIndex).getLast? =
        some (canonicalLiteralPosition
          placement orderedClause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (orderCanonicalRoutesByClauseDirection
          source placement family.routes clauseIndex literalIndex) := by
  rcases exists_sourceLiteral_of_orderedLiteral_mem
      family.routes clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      orderedClauseEq, literalEq, orderedRouteEq⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have sourceValid := family.endpoints
    sourceClause clauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
  have sourceOrthogonal := family.orthogonal
    sourceClause clauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
  subst orderedClause
  subst literal
  rw [orderCanonicalRoutesByClauseDirection, sourceClauseLookup,
    orderedRouteEq]
  constructor
  · simp only [PeriodicOrthocrossing.translatePolyline,
      List.head?_map, sourceValid.1, Option.map_some]
    apply congrArg some
    cases sourceAnchorEq :
        PeriodicCNF.clauseAnchor sourceClause.literals with
    | mk sourceAnchorX sourceAnchorY =>
      cases orderedAnchorEq : PeriodicCNF.clauseAnchor
        (orderClauseByRouteDirection
          family.routes clauseIndex sourceClause).literals with
      | mk orderedAnchorX orderedAnchorY =>
        simp [canonicalClausePosition,
          PeriodicVariablePlacement.translation,
          Cell.add, Cell.sub, Cell.scale,
          sourceAnchorEq, orderedAnchorEq]
        constructor <;> ring
  constructor
  · simp only [PeriodicOrthocrossing.translatePolyline,
      List.getLast?_map, sourceValid.2, Option.map_some]
    apply congrArg some
    cases sourceAnchorEq :
        PeriodicCNF.clauseAnchor sourceClause.literals with
    | mk sourceAnchorX sourceAnchorY =>
      cases orderedAnchorEq : PeriodicCNF.clauseAnchor
        (orderClauseByRouteDirection
          family.routes clauseIndex sourceClause).literals with
      | mk orderedAnchorX orderedAnchorY =>
        simp [canonicalLiteralPosition,
          PeriodicVariablePlacement.translation,
          Cell.add, Cell.sub, Cell.scale,
          sourceAnchorEq, orderedAnchorEq]
        constructor <;> ring
  · exact sourceOrthogonal.translate _

/-- Package the reordered, anchor-gauged routes behind the standard
canonical orthogonal route interface. -/
def CanonicalOrthogonalIncidenceRoutes.orderClausesByRouteDirection
    [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement) :
    CanonicalOrthogonalIncidenceRoutes
      (orderClausesByRouteDirection source family.routes) placement where
  routes :=
    orderCanonicalRoutesByClauseDirection source placement family.routes
  endpoints := by
    intro clause clauseIndex clauseMember literal literalIndex literalMember
    have valid := orderCanonicalRoutesByClauseDirection_valid
      placement family clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember literal literalIndex literalMember
    exact (orderCanonicalRoutesByClauseDirection_valid
      placement family clauseMember literalMember).2.2

/-- The anchor-gauge translation does not change the first direction of a
reindexed route selected by an explicit sorted-tag lookup. -/
theorem orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {sourceClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx)
    {taggedLiteral : PeriodicLiteral Variable × Nat}
    {literalIndex : Nat}
    (taggedLookup :
      (clauseLiteralOrder routes clauseIndex sourceClause)[literalIndex]? =
        some taggedLiteral) :
    AxisDirection.polylineFirstDirection
        (orderCanonicalRoutesByClauseDirection
          source placement routes clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (routes clauseIndex taggedLiteral.2) := by
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  simp [orderCanonicalRoutesByClauseDirection,
    orderRoutesByClauseDirection, sourceClauseLookup, taggedLookup]

/-- Route-order condition expected by a fixed three-port clause router. -/
def TernaryClauseRoutesInClockwiseOrder
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ clause clauseIndex,
    (clause, clauseIndex) ∈ source.clauses.zipIdx →
    clause.literals.length = 3 →
    AxisDirection.InClockwiseOrder
      (AxisDirection.polylineFirstDirection (routes clauseIndex 0))
      (AxisDirection.polylineFirstDirection (routes clauseIndex 1))
      (AxisDirection.polylineFirstDirection (routes clauseIndex 2))

/-- Stable rank sorting gives every ternary clause clockwise route order as
soon as the original genuine route directions are pairwise distinct within
that clause. -/
theorem orderCanonicalRoutesByClauseDirection_ternaryClockwise
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (genuine :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (AxisDirection.polylineFirstDirection
            (routes clauseIndex literalIndex)).IsGenuine)
    (distinct :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ first firstIndex,
          (first, firstIndex) ∈ clause.literals.zipIdx →
          ∀ second secondIndex,
            (second, secondIndex) ∈ clause.literals.zipIdx →
            firstIndex ≠ secondIndex →
            AxisDirection.polylineFirstDirection
                (routes clauseIndex firstIndex) ≠
              AxisDirection.polylineFirstDirection
                (routes clauseIndex secondIndex)) :
    TernaryClauseRoutesInClockwiseOrder
      (orderClausesByRouteDirection source routes)
      (orderCanonicalRoutesByClauseDirection source placement routes) := by
  intro orderedClause clauseIndex orderedClauseMember arity
  rcases exists_sourceClause_of_orderedClause_mem
      routes orderedClauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have sourceArity : sourceClause.literals.length = 3 := by
    rw [← orderClauseByRouteDirection_length
      routes clauseIndex sourceClause, ← orderedClauseEq]
    exact arity
  have orderLength :
      (clauseLiteralOrder routes clauseIndex sourceClause).length = 3 := by
    rw [show
      (clauseLiteralOrder routes clauseIndex sourceClause).length =
        sourceClause.literals.zipIdx.length by
          exact (clauseLiteralOrder_perm
            routes clauseIndex sourceClause).length_eq]
    simpa using sourceArity
  rcases List.length_eq_three.mp orderLength with
    ⟨first, second, third, orderEq⟩
  have firstMember : first ∈ sourceClause.literals.zipIdx :=
    (clauseLiteralOrder_perm routes clauseIndex sourceClause).mem_iff.mp
      (by simp [orderEq])
  have secondMember : second ∈ sourceClause.literals.zipIdx :=
    (clauseLiteralOrder_perm routes clauseIndex sourceClause).mem_iff.mp
      (by simp [orderEq])
  have thirdMember : third ∈ sourceClause.literals.zipIdx :=
    (clauseLiteralOrder_perm routes clauseIndex sourceClause).mem_iff.mp
      (by simp [orderEq])
  have orderedIndicesNodup :
      ((clauseLiteralOrder routes clauseIndex sourceClause).map
        Prod.snd).Nodup := by
    exact ((clauseLiteralOrder_perm
      routes clauseIndex sourceClause).map Prod.snd).nodup_iff.mpr
        (List.nodup_zipIdx_map_snd sourceClause.literals)
  rw [orderEq] at orderedIndicesNodup
  simp only [List.map_cons, List.map_nil,
    List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true, List.nodup_singleton] at orderedIndicesNodup
  have sorted := clauseLiteralOrder_pairwise
    routes clauseIndex sourceClause
  rw [orderEq] at sorted
  simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
    forall_eq_or_imp, forall_eq, List.pairwise_singleton] at sorted
  have clockwise := AxisDirection.inClockwiseOrder_of_rank_le
    (genuine sourceClause clauseIndex sourceClauseMember
      first.1 first.2 firstMember)
    (genuine sourceClause clauseIndex sourceClauseMember
      second.1 second.2 secondMember)
    (genuine sourceClause clauseIndex sourceClauseMember
      third.1 third.2 thirdMember)
    (distinct sourceClause clauseIndex sourceClauseMember
      first.1 first.2 firstMember second.1 second.2 secondMember
      orderedIndicesNodup.1.1)
    (distinct sourceClause clauseIndex sourceClauseMember
      first.1 first.2 firstMember third.1 third.2 thirdMember
      orderedIndicesNodup.1.2.1)
    (distinct sourceClause clauseIndex sourceClauseMember
      second.1 second.2 secondMember third.1 third.2 thirdMember
      orderedIndicesNodup.2.1.1)
    (by
      simpa [clauseLiteralDirectionLE, clauseLiteralDirectionRank] using
        sorted.1.1)
    (by
      simpa [clauseLiteralDirectionLE, clauseLiteralDirectionRank] using
        sorted.2.1)
  rw [orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
        (literalIndex := 0) (taggedLiteral := first) (by simp [orderEq]),
    orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
        (literalIndex := 1) (taggedLiteral := second) (by simp [orderEq]),
    orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
        (literalIndex := 2) (taggedLiteral := third) (by simp [orderEq])]
  exact clockwise

/-- Disjunction truth is insensitive to permuting a clause's literals. -/
theorem periodicClause_holds_iff_of_perm
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    {first second : PeriodicClause Variable}
    (permutation : first.Perm second) :
    first.Holds assignment translate ↔
      second.Holds assignment translate := by
  constructor
  · rintro ⟨literal, literalMember, holds⟩
    exact ⟨literal, permutation.mem_iff.mp literalMember, holds⟩
  · rintro ⟨literal, literalMember, holds⟩
    exact ⟨literal, permutation.mem_iff.mpr literalMember, holds⟩

/-- Reordering literals preserves satisfaction by each fixed assignment. -/
theorem orderClausesByRouteDirection_satisfies_iff
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (assignment : Variable → Cell → Bool) :
    (orderClausesByRouteDirection source routes).erase.Satisfies assignment ↔
      source.erase.Satisfies assignment := by
  constructor
  · intro satisfies translate clause clauseMember
    change clause ∈
      source.clauses.map PositionedPeriodicClause.literals at clauseMember
    rcases List.mem_map.mp clauseMember with
      ⟨sourceClause, sourceClauseMember, rfl⟩
    have indexedMember :
        sourceClause ∈ source.clauses.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using sourceClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEq⟩
    have orderedMember :=
      orderClauseByRouteDirection_mem routes taggedClauseMember
    have erasedOrderedMember :
        (orderClauseByRouteDirection routes taggedClause.2 taggedClause.1).literals ∈
          (orderClausesByRouteDirection source routes).erase.clauses := by
      change _ ∈
        (orderClausesByRouteDirection source routes).clauses.map
          PositionedPeriodicClause.literals
      exact List.mem_map.mpr
        ⟨_, List.fst_mem_of_mem_zipIdx orderedMember, rfl⟩
    have orderedHolds := satisfies translate _ erasedOrderedMember
    subst sourceClause
    exact (periodicClause_holds_iff_of_perm assignment translate
      (orderClauseByRouteDirection_literals_perm
        routes taggedClause.2 taggedClause.1)).mp orderedHolds
  · intro satisfies translate clause clauseMember
    change clause ∈
      (orderClausesByRouteDirection source routes).clauses.map
        PositionedPeriodicClause.literals at clauseMember
    rcases List.mem_map.mp clauseMember with
      ⟨orderedClause, orderedClauseMember, rfl⟩
    have indexedMember :
        orderedClause ∈
          (orderClausesByRouteDirection source routes).clauses.zipIdx.map
            Prod.fst := by
      simpa only [List.zipIdx_map_fst] using orderedClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEq⟩
    rcases exists_sourceClause_of_orderedClause_mem routes taggedClauseMember with
      ⟨sourceClause, sourceClauseMember, sourceClauseEq⟩
    have sourceHolds :
        sourceClause.literals.Holds assignment translate :=
      satisfies translate sourceClause.literals
        (by
          change sourceClause.literals ∈
            source.clauses.map PositionedPeriodicClause.literals
          exact List.mem_map.mpr
            ⟨sourceClause, List.fst_mem_of_mem_zipIdx sourceClauseMember, rfl⟩)
    subst orderedClause
    rw [sourceClauseEq]
    exact (periodicClause_holds_iff_of_perm assignment translate
      (orderClauseByRouteDirection_literals_perm
        routes taggedClause.2 sourceClause)).mpr sourceHolds

/-- Reordering literals preserves periodic satisfiability exactly. -/
theorem orderClausesByRouteDirection_satisfiable_iff
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    (orderClausesByRouteDirection source routes).erase.Satisfiable ↔
      source.erase.Satisfiable := by
  constructor <;>
    rintro ⟨assignment, satisfies⟩
  · exact ⟨assignment,
      (orderClausesByRouteDirection_satisfies_iff
        source routes assignment).mp satisfies⟩
  · exact ⟨assignment,
      (orderClausesByRouteDirection_satisfies_iff
        source routes assignment).mpr satisfies⟩

/-- Reordering preserves every uniform clause-width bound. -/
theorem orderClausesByRouteDirection_widthAtMost_iff
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) (width : Nat) :
    (orderClausesByRouteDirection source routes).erase.WidthAtMost width ↔
      source.erase.WidthAtMost width := by
  constructor
  · intro orderedWidth sourceClause sourceClauseMember
    change sourceClause ∈
      source.clauses.map PositionedPeriodicClause.literals at sourceClauseMember
    rcases List.mem_map.mp sourceClauseMember with
      ⟨positionedClause, positionedMember, rfl⟩
    have indexedMember :
        positionedClause ∈ source.clauses.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using positionedMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedMember, rfl⟩
    have orderedMember := orderClauseByRouteDirection_mem routes taggedMember
    have bound := orderedWidth
      (orderClauseByRouteDirection routes taggedClause.2 taggedClause.1).literals
      (by
        change _ ∈
          (orderClausesByRouteDirection source routes).clauses.map
            PositionedPeriodicClause.literals
        exact List.mem_map.mpr
          ⟨_, List.fst_mem_of_mem_zipIdx orderedMember, rfl⟩)
    simpa [PeriodicClause.WidthAtMost] using bound
  · intro sourceWidth orderedClause orderedClauseMember
    change orderedClause ∈
      (orderClausesByRouteDirection source routes).clauses.map
        PositionedPeriodicClause.literals at orderedClauseMember
    rcases List.mem_map.mp orderedClauseMember with
      ⟨positionedClause, positionedMember, rfl⟩
    have indexedMember :
        positionedClause ∈
          (orderClausesByRouteDirection source routes).clauses.zipIdx.map
            Prod.fst := by
      simpa only [List.zipIdx_map_fst] using positionedMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedMember, rfl⟩
    rcases exists_sourceClause_of_orderedClause_mem routes taggedMember with
      ⟨sourceClause, sourceMember, sourceClauseEq⟩
    have bound := sourceWidth sourceClause.literals
      (by
        change sourceClause.literals ∈
          source.clauses.map PositionedPeriodicClause.literals
        exact List.mem_map.mpr
          ⟨sourceClause, List.fst_mem_of_mem_zipIdx sourceMember, rfl⟩)
    rw [sourceClauseEq]
    simpa [PeriodicClause.WidthAtMost] using bound

/-- Per-clause atom distinctness is unchanged by literal reordering. -/
theorem orderClausesByRouteDirection_allAtomsNodup_iff
    [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    (orderClausesByRouteDirection source routes).AllAtomsNodup ↔
      source.AllAtomsNodup := by
  constructor
  · intro orderedDistinct sourceClause sourceClauseMember
    have indexedMember :
        sourceClause ∈ source.clauses.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using sourceClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedMember, rfl⟩
    have orderedMember := orderClauseByRouteDirection_mem routes taggedMember
    have distinct := orderedDistinct _
      (List.fst_mem_of_mem_zipIdx orderedMember)
    unfold PositionedPeriodicClause.AtomsNodup at distinct ⊢
    exact ((orderClauseByRouteDirection_literals_perm
      routes taggedClause.2 taggedClause.1).map
        PeriodicLiteral.atom).nodup_iff.mp distinct
  · intro sourceDistinct orderedClause orderedClauseMember
    have indexedMember :
        orderedClause ∈
          (orderClausesByRouteDirection source routes).clauses.zipIdx.map
            Prod.fst := by
      simpa only [List.zipIdx_map_fst] using orderedClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedMember, rfl⟩
    rcases exists_sourceClause_of_orderedClause_mem routes taggedMember with
      ⟨sourceClause, sourceMember, sourceClauseEq⟩
    have distinct := sourceDistinct sourceClause
      (List.fst_mem_of_mem_zipIdx sourceMember)
    unfold PositionedPeriodicClause.AtomsNodup at distinct ⊢
    rw [sourceClauseEq]
    exact ((orderClauseByRouteDirection_literals_perm
      routes taggedClause.2 sourceClause).map
        PeriodicLiteral.atom).nodup_iff.mpr distinct

end PositionedPeriodicCNF
end LeanTrominoes
