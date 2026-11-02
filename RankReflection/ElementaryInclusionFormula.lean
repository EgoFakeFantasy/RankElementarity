import RankReflection.TruthAgreement
import Mathlib.Tactic.FinCases

/-! A finite pure membership formula expressing `V_alpha ≺ V_delta`, with its full semantic
correctness. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- The syntax books do not depend on the rank domain they are taken in. -/
theorem rankSyntaxBooks_val {alpha beta : Ordinal.{u}}
    (hAlpha : Ordinal.omega0 < alpha) (hBeta : Ordinal.omega0 < beta) (i : Fin 6) :
    (rankSyntaxBooks hAlpha i).val = (rankSyntaxBooks hBeta i).val := by
  fin_cases i <;> rfl

/-- The six books occupy positions 0–5, the two domains positions 6–7,
and the two truth sets positions 8–9. All quantifiers are first-order. -/
def elementaryInclusionBody : RankPredicateFormula 0 10 :=
  (setRelativize rankTruthMatrix (Fin.castAdd 4) (fun _ => 8) 6).and
    ((setRelativize rankTruthMatrix (Fin.castAdd 4) (fun _ => 9) 7).and
      (setRelativize truthAgreementMatrix (Fin.castAdd 4) ![8, 9] 6))

/-- A finite pure membership formula for full elementary inclusion of two
set-sized rank domains. The two truth sets are quantified, not postulated. -/
def elementaryInclusionFormula : RankPredicateFormula 0 8 := elementaryInclusionBody.ex.ex

/-- Semantics of `elementaryInclusionBody`: both truth sets satisfy the truth conditions, and they
agree. -/
theorem elementaryInclusionBody_realize {alpha delta eta : Ordinal.{u}}
    (hAlphaEta : alpha < eta) (hDeltaEta : delta < eta)
    (hAlpha : Order.IsSuccLimit alpha) (hDelta : Order.IsSuccLimit delta)
    (hOmegaAlpha : Ordinal.omega0 < alpha) (hOmegaDelta : Ordinal.omega0 < delta)
    (outer : Fin 10 → RankDomain eta)
    (hBooks : ∀ i : Fin 6, (outer (i.castAdd 4)).val = (rankSyntaxBooks hOmegaAlpha i).val)
    (hA : (outer 6).val = ZFSet.vonNeumann alpha)
    (hD : (outer 7).val = ZFSet.vonNeumann delta) :
    elementaryInclusionBody.Realize Fin.elim0 outer ↔
      RankTruthConditions hAlpha (fun x => x.val ∈ (outer 8).val) ∧
      RankTruthConditions hDelta (fun x => x.val ∈ (outer 9).val) ∧
      RankTruthAgreement hAlpha (fun x => x.val ∈ (outer 8).val)
        (fun x => x.val ∈ (outer 9).val) := by
  have hSmall := setRelativize_realize hAlphaEta.le rankTruthMatrix
    (Fin.castAdd 4) (fun _ => (8 : Fin 10)) 6
    (fun _ x => x.val ∈ (outer 8).val) (rankSyntaxBooks hOmegaAlpha) outer
    hBooks (fun _ _ => Iff.rfl) hA
  have hLarge := setRelativize_realize hDeltaEta.le rankTruthMatrix
    (Fin.castAdd 4) (fun _ => (9 : Fin 10)) 7
    (fun _ x => x.val ∈ (outer 9).val) (rankSyntaxBooks hOmegaDelta) outer
    (fun i => (hBooks i).trans (rankSyntaxBooks_val hOmegaAlpha hOmegaDelta i))
    (fun _ _ => Iff.rfl) hD
  have hCompare := setRelativize_realize hAlphaEta.le truthAgreementMatrix
    (Fin.castAdd 4) ![8, 9] 6
    ![(fun x => x.val ∈ (outer 8).val), (fun x => x.val ∈ (outer 9).val)]
    (rankSyntaxBooks hOmegaAlpha) outer hBooks (by intro a x; fin_cases a <;> rfl) hA
  simp only [elementaryInclusionBody, RankPredicateFormula.realize_and]
  rw [hSmall, hLarge, hCompare, rankTruthMatrix_correct hAlpha hOmegaAlpha,
    rankTruthMatrix_correct hDelta hOmegaDelta, truthAgreementMatrix_realize hAlpha hOmegaAlpha]

/-- `elementaryInclusionBody_realize` with the two truth sets appended as the last two slots. -/
theorem elementaryInclusionBody_snoc_realize {alpha delta eta : Ordinal.{u}}
    (hAlphaEta : alpha < eta) (hDeltaEta : delta < eta)
    (hAlpha : Order.IsSuccLimit alpha) (hDelta : Order.IsSuccLimit delta)
    (hOmegaAlpha : Ordinal.omega0 < alpha) (hOmegaDelta : Ordinal.omega0 < delta)
    (outer : Fin 8 → RankDomain eta)
    (hBooks : ∀ i : Fin 6, (outer (i.castAdd 2)).val = (rankSyntaxBooks hOmegaAlpha i).val)
    (hA : (outer 6).val = ZFSet.vonNeumann alpha)
    (hD : (outer 7).val = ZFSet.vonNeumann delta)
    (left right : RankDomain eta) :
    elementaryInclusionBody.Realize Fin.elim0 (Fin.snoc (Fin.snoc outer left) right) ↔
      RankTruthConditions hAlpha (fun x => x.val ∈ left.val) ∧
      RankTruthConditions hDelta (fun x => x.val ∈ right.val) ∧
      RankTruthAgreement hAlpha (fun x => x.val ∈ left.val) (fun x => x.val ∈ right.val) := by
  let extended : Fin 10 → RankDomain eta := Fin.snoc (Fin.snoc outer left) right
  have hBooks' (i : Fin 6) :
      (extended (i.castAdd 4)).val =
        (rankSyntaxBooks hOmegaAlpha i).val := by
    change (extended ((i.castAdd 2).castSucc.castSucc)).val = _
    simpa only [extended, Fin.snoc_castSucc] using hBooks i
  have hA' : (extended 6).val = ZFSet.vonNeumann alpha := by
    simpa [extended, Fin.snoc] using hA
  have hD' : (extended 7).val = ZFSet.vonNeumann delta := by
    simpa [extended, Fin.snoc] using hD
  simpa [extended, Fin.snoc] using elementaryInclusionBody_realize hAlphaEta hDeltaEta hAlpha hDelta
    hOmegaAlpha hOmegaDelta extended hBooks' hA' hD'

/-- Full semantic correctness of the finite elementary-inclusion formula
inside a larger actual rank domain. No definability assumption occurs. -/
theorem elementaryInclusionFormula_realize {alpha delta eta : Ordinal.{u}}
    (hAlphaDelta : alpha ≤ delta) (hDeltaEta : delta < eta)
    (hAlpha : Order.IsSuccLimit alpha) (hDelta : Order.IsSuccLimit delta)
    (hOmegaAlpha : Ordinal.omega0 < alpha) (hOmegaDelta : Ordinal.omega0 < delta)
    (outer : Fin 8 → RankDomain eta)
    (hBooks : ∀ i : Fin 6, (outer (i.castAdd 2)).val = (rankSyntaxBooks hOmegaAlpha i).val)
    (hA : (outer 6).val = ZFSet.vonNeumann alpha)
    (hD : (outer 7).val = ZFSet.vonNeumann delta) :
    elementaryInclusionFormula.Realize Fin.elim0 outer ↔
      RankElementaryInclusion alpha delta := by
  have hAlphaEta := hAlphaDelta.trans_lt hDeltaEta
  simp only [elementaryInclusionFormula, RankPredicateFormula.realize_ex]
  constructor
  · rintro ⟨left, right, hBody⟩
    obtain ⟨hLeft, hRight, hAgreement⟩ :=
      (elementaryInclusionBody_snoc_realize hAlphaEta hDeltaEta hAlpha hDelta
        hOmegaAlpha hOmegaDelta outer hBooks hA hD left right).mp hBody
    exact (rankTruthAgreement_iff_inclusion hAlphaDelta hAlpha hDelta
      (fun x => x.val ∈ left.val) (fun x => x.val ∈ right.val) hLeft hRight).mp hAgreement
  · intro hElem
    let left := rankClassSetIn hAlphaEta (rankSatisfaction hAlpha)
    let right := rankClassSetIn hDeltaEta (rankSatisfaction hDelta)
    have hLeftEq : (fun x : RankDomain alpha => x.val ∈ left.val) = rankSatisfaction hAlpha := by
      funext x
      exact propext (rankClassSet_mem _ x)
    have hRightEq : (fun x : RankDomain delta => x.val ∈ right.val) = rankSatisfaction hDelta := by
      funext x
      exact propext (rankClassSet_mem _ x)
    have hLeft : RankTruthConditions hAlpha (fun x => x.val ∈ left.val) := by
      rw [hLeftEq]
      exact rankSatisfaction_conditions hAlpha
    have hRight : RankTruthConditions hDelta (fun x => x.val ∈ right.val) := by
      rw [hRightEq]
      exact rankSatisfaction_conditions hDelta
    refine ⟨left, right, (elementaryInclusionBody_snoc_realize hAlphaEta hDeltaEta hAlpha hDelta
      hOmegaAlpha hOmegaDelta outer hBooks hA hD left right).mpr ⟨hLeft, hRight, ?_⟩⟩
    exact (rankTruthAgreement_iff_inclusion hAlphaDelta hAlpha hDelta
      (fun x => x.val ∈ left.val) (fun x => x.val ∈ right.val) hLeft hRight).mpr hElem

end RankReflection
