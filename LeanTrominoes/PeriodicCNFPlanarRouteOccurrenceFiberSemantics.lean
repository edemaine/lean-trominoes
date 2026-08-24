/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilterMapKey
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberData
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceOrder

/-! # Exact per-incidence routed-occurrence fibers -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The site-selected occurrence list is the incidence-order concatenation
of its per-incidence neighboring-translation fibers. -/
theorem variableRouteOccurrencesAt_eq_flatMap_fibers
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    variableRouteOccurrencesAt formula site =
      (PeriodicCNF.incidencesWithMetadata formula).zipIdx.flatMap
        fun taggedIncidence =>
          translatedIncidenceOccurrencesAt taggedIncidence site := by
  rw [variableRouteOccurrencesAt_eq_filter]
  unfold drawingCNFRouteOccurrences
    translatedIncidenceOccurrencesAt
  rw [List.filter_flatMap]

/-- One indexed incidence contributes either its unique translation at
`site - offset`, or no occurrence when the atom/translation is absent. -/
theorem translatedIncidenceOccurrencesAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (taggedIncidence : CNFIncidence Variable × Nat)
    (site : VariableRouteSite Variable) :
    translatedIncidenceOccurrencesAt taggedIncidence site =
      if taggedIncidence.1.literal.atom = site.1 then
        let translate := Cell.sub site.2 taggedIncidence.1.edge.offset
        if translate ∈ neighborTranslations then
          [⟨taggedIncidence.1, taggedIncidence.2, translate⟩]
        else
          []
      else
        [] := by
  by_cases sameAtom : taggedIncidence.1.literal.atom = site.1
  · rw [if_pos sameAtom]
    let translate := Cell.sub site.2 taggedIncidence.1.edge.offset
    let occurrence : CNFRouteOccurrence Variable :=
      ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
    have occurrenceSite : occurrence.variableOccurrence = site := by
      apply Prod.ext
      · exact sameAtom
      · simp [occurrence, translate, CNFRouteOccurrence.variableOccurrence,
          CNFRouteOccurrence.edge, Cell.add, Cell.sub]
    have keyInjective : Function.Injective
        (CNFRouteOccurrence.variableOccurrence ∘
          fun selectedTranslate =>
            (⟨taggedIncidence.1, taggedIncidence.2, selectedTranslate⟩ :
              CNFRouteOccurrence Variable)) := by
      intro first second keyEquality
      have positionEquality := congrArg Prod.snd keyEquality
      rcases first with ⟨firstHorizontal, firstVertical⟩
      rcases second with ⟨secondHorizontal, secondVertical⟩
      simp only [Function.comp_apply,
        CNFRouteOccurrence.variableOccurrence, CNFRouteOccurrence.edge,
        Cell.add, Prod.mk.injEq] at positionEquality ⊢
      exact
        ⟨Int.add_left_cancel (a := taggedIncidence.1.edge.offset.1)
            (by simpa [Int.add_comm] using positionEquality.1),
          Int.add_left_cancel (a := taggedIncidence.1.edge.offset.2)
            (by simpa [Int.add_comm] using positionEquality.2)⟩
    change
      (neighborTranslations.map fun selectedTranslate =>
        (⟨taggedIncidence.1, taggedIncidence.2, selectedTranslate⟩ :
          CNFRouteOccurrence Variable)).filter
          (fun selectedOccurrence =>
            selectedOccurrence.variableOccurrence = site) =
        if translate ∈ neighborTranslations then [occurrence] else []
    rw [← occurrenceSite]
    have filtered := filter_map_key_eq neighborTranslations
      (by native_decide)
      (fun selectedTranslate =>
        (⟨taggedIncidence.1, taggedIncidence.2, selectedTranslate⟩ :
          CNFRouteOccurrence Variable))
      CNFRouteOccurrence.variableOccurrence keyInjective translate
    by_cases translateMember : translate ∈ neighborTranslations
    · rw [if_pos translateMember] at filtered ⊢
      simpa [occurrence] using filtered
    · rw [if_neg translateMember] at filtered ⊢
      exact filtered
  · rw [if_neg sameAtom]
    unfold translatedIncidenceOccurrencesAt
    rw [List.filter_eq_nil_iff]
    intro occurrence occurrenceMember reachesSite
    have siteEquality : occurrence.variableOccurrence = site :=
      of_decide_eq_true reachesSite
    rcases List.mem_map.mp occurrenceMember with
      ⟨translate, _translateMember, occurrenceEq⟩
    subst occurrence
    exact sameAtom (congrArg Prod.fst siteEquality)

end LeanTrominoes.PeriodicOrthocrossing
