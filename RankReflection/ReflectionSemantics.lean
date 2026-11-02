import RankReflection.ReflectionFormula

/-! The meaning of the reflection formula: an elementary extension of `V_alpha` exists below the
ambient height. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- The reflected finite formula means the actual existence of a higher
elementary rank extension below the ambient height. All coding and hierarchy
witnesses have been eliminated from the mathematical conclusion. -/
theorem reflectionFormula_realize {alpha xi eta : Ordinal.{u}}
    (hEta : Order.IsSuccLimit eta) (hAlpha : Order.IsSuccLimit alpha)
    (hOmegaAlpha : Ordinal.omega0 < alpha) (outer : Fin 9 → RankDomain eta)
    (hBooks : ∀ i : Fin 6, (outer (i.castAdd 3)).val = (rankSyntaxBooks hOmegaAlpha i).val)
    (hA : (outer 6).val = ZFSet.vonNeumann alpha)
    (hIndex : (outer 7).val = alpha.toZFSet) (hBound : (outer 8).val = xi.toZFSet) :
    reflectionFormula.Realize Fin.elim0 outer ↔
      ∃ delta : Ordinal.{u}, max alpha xi < delta ∧ delta < eta ∧
        Order.IsSuccLimit delta ∧ RankElementaryInclusion alpha delta := by
  rw [reflectionFormula_realize_raw]
  have hBooksE (domain : RankDomain eta) (i : Fin 6) :
      ((reflectionElementaryValues outer domain) (i.castAdd 2)).val =
        (rankSyntaxBooks hOmegaAlpha i).val := by
    simpa only [reflectionElementaryValues, Fin.append_left] using hBooks i
  have hAE (domain : RankDomain eta) :
      ((reflectionElementaryValues outer domain) 6).val = ZFSet.vonNeumann alpha := by
    simpa [reflectionElementaryValues] using hA
  constructor
  · rintro ⟨index, domain, hAboveAlpha, hAboveXi, hLimit, hHierarchy, hElementary⟩
    have hHierarchy' := (hierarchyFormula_realize hEta ![index, domain]).mp hHierarchy
    change ZFSet.IsOrdinal index.val ∧ domain.val = ZFSet.vonNeumann index.val.rank at hHierarchy'
    obtain ⟨hOrdinal, hDomain⟩ := hHierarchy'
    let delta := index.val.rank
    have hCode : delta.toZFSet = index.val := hOrdinal.toZFSet_rank_eq
    rw [hIndex, ← hCode] at hAboveAlpha
    rw [hBound, ← hCode] at hAboveXi
    have hAlphaDelta : alpha < delta := Ordinal.toZFSet_mem_toZFSet_iff.mp hAboveAlpha
    have hXiDelta : xi < delta := Ordinal.toZFSet_mem_toZFSet_iff.mp hAboveXi
    have hDeltaEta : delta < eta := index.property
    have hSame : ordinalDomainElement (⟨delta, hDeltaEta⟩ : OrdinalDomain eta) = index :=
      Subtype.ext hCode
    rw [← hSame] at hLimit
    have hDelta : Order.IsSuccLimit delta := (rankIsNonzeroLimit_ordinal_iff _).mp hLimit
    have hDE : ((reflectionElementaryValues outer domain) 7).val = ZFSet.vonNeumann delta := by
      simpa [reflectionElementaryValues] using hDomain
    have hElem := (elementaryInclusionFormula_realize hAlphaDelta.le hDeltaEta hAlpha hDelta
      hOmegaAlpha (hOmegaAlpha.trans hAlphaDelta) (reflectionElementaryValues outer domain)
      (hBooksE domain) (hAE domain) hDE).mp hElementary
    exact ⟨delta, max_lt hAlphaDelta hXiDelta, hDeltaEta, hDelta, hElem⟩
  · rintro ⟨delta, hAbove, hDeltaEta, hDelta, hElem⟩
    obtain ⟨hAlphaDelta, hXiDelta⟩ := max_lt_iff.mp hAbove
    let index := ordinalDomainElement (⟨delta, hDeltaEta⟩ : OrdinalDomain eta)
    let domain := rankDomainSet hDeltaEta
    have hDE : ((reflectionElementaryValues outer domain) 7).val = ZFSet.vonNeumann delta := rfl
    refine ⟨index, domain, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hIndex]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hAlphaDelta
    · rw [hBound]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hXiDelta
    · exact (rankIsNonzeroLimit_ordinal_iff (⟨delta, hDeltaEta⟩ : OrdinalDomain eta)).mpr hDelta
    · apply (hierarchyFormula_realize hEta ![index, domain]).mpr
      refine ⟨ZFSet.isOrdinal_toZFSet _, ?_⟩
      simp [index, domain, ordinalDomainElement, rankDomainSet]
    · exact (elementaryInclusionFormula_realize hAlphaDelta.le hDeltaEta hAlpha hDelta
        hOmegaAlpha (hOmegaAlpha.trans hAlphaDelta) (reflectionElementaryValues outer domain)
        (hBooksE domain) (hAE domain) hDE).mpr hElem

end RankReflection
