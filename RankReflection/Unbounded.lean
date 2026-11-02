import RankReflection.ReflectionSemantics

/-! Main theorems: elementary extensions of `V_alpha` are unbounded below `beta`, first for ordinals
and then for cardinals. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- Three strictly increasing actual rank domains with elementary natural
inclusions yield elementary extensions of the first domain unbounded below
the middle height. The heights need not be cardinals. -/
theorem exists_rankElementaryInclusion_between {alpha beta gamma : Ordinal.{u}}
    (hAB : alpha < beta) (hBC : beta < gamma)
    (hElemAB : RankElementaryInclusion alpha beta)
    (hElemBC : RankElementaryInclusion beta gamma)
    {xi : Ordinal.{u}} (hXi : xi < beta) :
    ∃ delta : Ordinal.{u}, max alpha xi < delta ∧ delta < beta ∧
      RankElementaryInclusion alpha delta := by
  have hAlpha := hElemAB.isSuccLimit_source hAB
  have hBeta := hElemBC.isSuccLimit_source hBC
  have hGamma := hElemBC.isSuccLimit_target hBC
  have hOmegaAlpha := hElemAB.omega_lt_source hAB
  have hOmegaBeta := hOmegaAlpha.trans hAB
  let parameters : Fin 9 → RankDomain beta :=
    Fin.append (rankSyntaxBooks hOmegaBeta)
      ![rankDomainSet hAB, ordinalDomainElement ⟨alpha, hAB⟩, ordinalDomainElement ⟨xi, hXi⟩]
  have hBooks (i : Fin 6) : (parameters (i.castAdd 3)).val = (rankSyntaxBooks hOmegaAlpha i).val := by
    simpa only [parameters, Fin.append_left] using rankSyntaxBooks_val hOmegaBeta hOmegaAlpha i
  have hA : (parameters 6).val = ZFSet.vonNeumann alpha := rfl
  have hIndex : (parameters 7).val = alpha.toZFSet := rfl
  have hBound : (parameters 8).val = xi.toZFSet := rfl
  have hUpper : reflectionFormula.Realize Fin.elim0 (rankInclusion hBC.le ∘ parameters) := by
    apply (reflectionFormula_realize hGamma hAlpha hOmegaAlpha
      (rankInclusion hBC.le ∘ parameters) hBooks hA hIndex hBound).mpr
    exact ⟨beta, max_lt hAB hXi, hBC, hBeta, hElemAB⟩
  have hLower := (hElemBC.map_predicateFormula hBC.le reflectionFormula parameters).mp hUpper
  obtain ⟨delta, hAbove, hBelow, _, hElem⟩ :=
    (reflectionFormula_realize hBeta hAlpha hOmegaAlpha parameters hBooks hA hIndex hBound).mp hLower
  exact ⟨delta, hAbove, hBelow, hElem⟩

/-- The requested cardinal theorem: the ordinals delta below b for which
V_a is an elementary substructure of V_delta are unbounded in b. -/
theorem rankElementaryInclusion_unbounded {a b c : Cardinal.{u}}
    (hAB : a < b) (hBC : b < c)
    (hElemAB : RankElementaryInclusion a.ord b.ord)
    (hElemBC : RankElementaryInclusion b.ord c.ord) :
    ∀ xi : Ordinal.{u}, xi < b.ord → ∃ delta : Ordinal.{u},
      xi < delta ∧ delta < b.ord ∧ RankElementaryInclusion a.ord delta := by
  intro xi hXi
  obtain ⟨delta, hAbove, hBelow, hElem⟩ := exists_rankElementaryInclusion_between
    (Cardinal.ord_lt_ord.mpr hAB) (Cardinal.ord_lt_ord.mpr hBC) hElemAB hElemBC hXi
  exact ⟨delta, (max_lt_iff.mp hAbove).2, hBelow, hElem⟩

end RankReflection
