import LeanTrominoes.PlanarOneInThreeFigureNineInstantiation
import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.PlanarOneInThreeNoUnitsInstantiation

/-!
# Instantiating Figure 9 at positioned periodic clauses

The finite Figure 9 instances use an offset-zero copy of their source clause
to scope fresh auxiliary variables.  A genuine positioned periodic source
may have nonzero literal offsets, and those offsets are part of the actual
auxiliary name.

This module transports a certified finite instance through a bijective swap
of the old and actual auxiliary scopes.  Thus routes and coordinates stay
unchanged while the embedded formula becomes the real positioned
`clauseGadget` output after forgetting only literal offsets.
-/

namespace LeanTrominoes
namespace PlanarOneInThreePositioned

open PlanarThreeSAT

/-- Bijectively exchange two Figure 9 auxiliary scopes while leaving source
atoms and auxiliary roles unchanged. -/
def rescopeEquiv {Variable : Type*} [DecidableEq Variable]
    (oldScope newScope : Nat × PeriodicClause Variable) :
    OneInThreeVariable Variable ≃
      OneInThreeVariable Variable :=
  Equiv.sumCongr (Equiv.refl Variable)
    (Equiv.prodCongr
      (Equiv.swap oldScope newScope)
      (Equiv.refl OneInThreeAux))

@[simp]
theorem rescopeEquiv_source
    {Variable : Type*} [DecidableEq Variable]
    (oldScope newScope : Nat × PeriodicClause Variable)
    (atom : Variable) :
    rescopeEquiv oldScope newScope (.inl atom) =
      .inl atom := by
  rfl

@[simp]
theorem rescopeEquiv_oldScope
    {Variable : Type*} [DecidableEq Variable]
    (oldScope newScope : Nat × PeriodicClause Variable)
    (kind : OneInThreeAux) :
    rescopeEquiv oldScope newScope
        (.inr (oldScope, kind)) =
      .inr (newScope, kind) := by
  simp [rescopeEquiv]

/-- Transport a finite Figure 9 drawing through a scope swap.  Pulling the
old placement back through the inverse equivalence leaves all route geometry
unchanged. -/
def rescopeDrawing {Variable : Type*} [DecidableEq Variable]
    (drawing :
      EmbeddedCNFIncidenceDrawing
        (OneInThreeVariable Variable))
    (oldScope newScope : Nat × PeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  drawing.rename
    (rescopeEquiv oldScope newScope)
    (fun target =>
      drawing.variablePosition
        ((rescopeEquiv oldScope newScope).symm target))

/-- A bijective scope change preserves the complete finite drawing
certificate. -/
theorem rescopeDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (drawing :
      EmbeddedCNFIncidenceDrawing
        (OneInThreeVariable Variable))
    (oldScope newScope : Nat × PeriodicClause Variable)
    (valid : drawing.IsValid) :
    (rescopeDrawing drawing oldScope newScope).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro first _firstMember second _secondMember equal
    exact (rescopeEquiv oldScope newScope).injective equal
  · intro atom _atomMember
    exact congrArg drawing.variablePosition
      ((rescopeEquiv oldScope newScope).symm_apply_apply atom)
  · exact valid

/-- The embedded form of a positioned source clause. -/
def embeddedSource {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    EmbeddedClause Variable :=
  PlanarOneInThreeNoUnits.embedPositionedClause source

/-- Certified ternary Figure 9 drawing with auxiliaries scoped by the actual
positioned periodic source clause. -/
def instantiatedThreeDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let embedded := embeddedSource source
  rescopeDrawing
    (PlanarOneInThree.instantiatedThreeDrawing
      source.position clauseIndex
      first.atom first.value
      second.atom second.value
      third.atom third.value)
    (clauseIndex, PlanarOneInThree.zeroOffsetClause embedded)
    (clauseIndex, source.literals)

/-- The positioned ternary instance embeds exactly the genuine output
clause block. -/
theorem instantiatedThreeDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (sourceLiterals :
      source.literals = [first, second, third]) :
    (instantiatedThreeDrawing clauseIndex source
      first second third).formula =
      (PeriodicOneInThreePositioned.clauseGadget
        clauseIndex source).map
          PlanarOneInThreeNoUnits.embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  unfold instantiatedThreeDrawing rescopeDrawing
  dsimp only [embeddedSource,
    EmbeddedCNFIncidenceDrawing.rename]
  rw [PlanarOneInThree.instantiatedThreeDrawing_formula]
  simp [PlanarOneInThree.clauseGadget,
    PlanarOneInThree.threeSourceClause,
    PeriodicOneInThreePositioned.clauseGadget,
    PlanarOneInThree.zeroOffsetClause,
    PlanarOneInThree.embedGeneratedClause,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    EmbeddedClause.rename, EmbeddedClause.map,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate]

/-- Pairwise distinct ternary source atoms give a valid positioned Figure 9
instance. -/
theorem instantiatedThreeDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (firstNeThird : first.atom ≠ third.atom)
    (secondNeThird : second.atom ≠ third.atom) :
    (instantiatedThreeDrawing clauseIndex source
      first second third).IsValid := by
  apply rescopeDrawing_isValid
  exact PlanarOneInThree.instantiatedThreeDrawing_isValid
    source.position clauseIndex
    first.atom first.value
    second.atom second.value
    third.atom third.value
    firstNeSecond firstNeThird secondNeThird

/-! ## Binary source clauses -/

/-- Certified binary Figure 9 drawing with the actual positioned auxiliary
scope. -/
def instantiatedTwoDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let embedded := embeddedSource source
  rescopeDrawing
    (PlanarOneInThree.instantiatedTwoDrawing
      source.position clauseIndex
      first.atom first.value
      second.atom second.value)
    (clauseIndex, PlanarOneInThree.zeroOffsetClause embedded)
    (clauseIndex, source.literals)

theorem instantiatedTwoDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (sourceLiterals :
      source.literals = [first, second]) :
    (instantiatedTwoDrawing clauseIndex source
      first second).formula =
      (PeriodicOneInThreePositioned.clauseGadget
        clauseIndex source).map
          PlanarOneInThreeNoUnits.embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  unfold instantiatedTwoDrawing rescopeDrawing
  dsimp only [embeddedSource,
    EmbeddedCNFIncidenceDrawing.rename]
  rw [PlanarOneInThree.instantiatedTwoDrawing_formula]
  simp [PlanarOneInThree.clauseGadget,
    PlanarOneInThree.twoSourceClause,
    PeriodicOneInThreePositioned.clauseGadget,
    PlanarOneInThree.zeroOffsetClause,
    PlanarOneInThree.embedGeneratedClause,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    EmbeddedClause.rename, EmbeddedClause.map,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate]

theorem instantiatedTwoDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom) :
    (instantiatedTwoDrawing clauseIndex source
      first second).IsValid := by
  apply rescopeDrawing_isValid
  exact PlanarOneInThree.instantiatedTwoDrawing_isValid
    source.position clauseIndex
    first.atom first.value
    second.atom second.value
    firstNeSecond

/-! ## Unit source clauses -/

/-- Certified unit Figure 9 drawing with the actual positioned auxiliary
scope. -/
def instantiatedOneDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let embedded := embeddedSource source
  rescopeDrawing
    (PlanarOneInThree.instantiatedOneDrawing
      source.position clauseIndex
      first.atom first.value)
    (clauseIndex, PlanarOneInThree.zeroOffsetClause embedded)
    (clauseIndex, source.literals)

theorem instantiatedOneDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable)
    (sourceLiterals : source.literals = [first]) :
    (instantiatedOneDrawing clauseIndex source first).formula =
      (PeriodicOneInThreePositioned.clauseGadget
        clauseIndex source).map
          PlanarOneInThreeNoUnits.embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  unfold instantiatedOneDrawing rescopeDrawing
  dsimp only [embeddedSource,
    EmbeddedCNFIncidenceDrawing.rename]
  rw [PlanarOneInThree.instantiatedOneDrawing_formula]
  simp [PlanarOneInThree.clauseGadget,
    PlanarOneInThree.oneSourceClause,
    PeriodicOneInThreePositioned.clauseGadget,
    PlanarOneInThree.zeroOffsetClause,
    PlanarOneInThree.embedGeneratedClause,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    EmbeddedClause.rename, EmbeddedClause.map,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate]

theorem instantiatedOneDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    (instantiatedOneDrawing clauseIndex source
      first).IsValid := by
  apply rescopeDrawing_isValid
  exact PlanarOneInThree.instantiatedOneDrawing_isValid
    source.position clauseIndex first.atom first.value

/-! ## Empty source clauses -/

/-- Certified empty Figure 9 drawing with the actual positioned auxiliary
scope. -/
def instantiatedZeroDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let embedded := embeddedSource source
  rescopeDrawing
    (PlanarOneInThree.instantiatedZeroDrawing
      (Variable := Variable) source.position clauseIndex)
    (clauseIndex, PlanarOneInThree.zeroOffsetClause embedded)
    (clauseIndex, source.literals)

theorem instantiatedZeroDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (sourceLiterals : source.literals = []) :
    (instantiatedZeroDrawing clauseIndex source).formula =
      (PeriodicOneInThreePositioned.clauseGadget
        clauseIndex source).map
          PlanarOneInThreeNoUnits.embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  unfold instantiatedZeroDrawing rescopeDrawing
  dsimp only [embeddedSource,
    EmbeddedCNFIncidenceDrawing.rename]
  rw [PlanarOneInThree.instantiatedZeroDrawing_formula]
  simp [PlanarOneInThree.clauseGadget,
    PlanarOneInThree.zeroSourceClause,
    PeriodicOneInThreePositioned.clauseGadget,
    PlanarOneInThree.zeroOffsetClause,
    PlanarOneInThree.embedGeneratedClause,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    EmbeddedClause.rename, EmbeddedClause.map,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate]

theorem instantiatedZeroDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    (instantiatedZeroDrawing clauseIndex
      source).IsValid := by
  apply rescopeDrawing_isValid
  exact PlanarOneInThree.instantiatedZeroDrawing_isValid
    source.position clauseIndex

/-! ## Uniform arity selector -/

/-- Select the certified positioned Figure 9 instance determined by a source
clause's arity.  Inputs beyond width three use the ternary prefix as a total
fallback; the exactness and validity theorems below assume width at most
three. -/
def instantiatedDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  match source.literals with
  | [] => instantiatedZeroDrawing clauseIndex source
  | [first] =>
      instantiatedOneDrawing clauseIndex source first
  | [first, second] =>
      instantiatedTwoDrawing clauseIndex source first second
  | first :: second :: third :: _ =>
      instantiatedThreeDrawing clauseIndex source
        first second third

/-- For a width-three source, the selected local drawing embeds exactly the
actual positioned Figure 9 output block. -/
theorem instantiatedDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing clauseIndex source).formula =
      (PeriodicOneInThreePositioned.clauseGadget
        clauseIndex source).map
          PlanarOneInThreeNoUnits.embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_formula
      clauseIndex ⟨sourcePosition, []⟩ rfl
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_formula
        clauseIndex ⟨sourcePosition, [first]⟩ first rfl
    · rcases rest with _ | ⟨third, tail⟩
      · exact instantiatedTwoDrawing_formula
          clauseIndex
          ⟨sourcePosition, [first, second]⟩
          first second rfl
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        exact instantiatedThreeDrawing_formula
          clauseIndex
          ⟨sourcePosition, [first, second, third]⟩
          first second third rfl

/-- Width at most three and pairwise distinct source atoms make the selected
positioned Figure 9 drawing valid. -/
theorem instantiatedDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    (instantiatedDrawing clauseIndex source).IsValid := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_isValid
      clauseIndex ⟨sourcePosition, []⟩
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_isValid
        clauseIndex ⟨sourcePosition, [first]⟩ first
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedTwoDrawing_isValid
          clauseIndex
          ⟨sourcePosition, [first, second]⟩
          first second firstNeSecond
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedThreeDrawing_isValid
          clauseIndex
          ⟨sourcePosition, [first, second, third]⟩
          first second third
          pairwise.1.1 pairwise.1.2 pairwise.2

end PlanarOneInThreePositioned
end LeanTrominoes
