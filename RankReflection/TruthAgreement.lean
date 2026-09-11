import RankReflection.SetSatisfaction

namespace RankReflection

open FullMarkedBLP

universe u

theorem rankAssignment_inclusion_val {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    (hAlpha : Order.IsSuccLimit alpha) (hBeta : Order.IsSuccLimit beta)
    {n : Nat} (values : Fin n → RankDomain alpha) :
    (rankAssignment hBeta (rankInclusion hAB ∘ values)).val =
      (rankAssignment hAlpha values).val := by
  apply ZFSet.ext
  intro z
  simp only [rankAssignment_mem_iff, Function.comp_apply, rankInclusion_val]

theorem rankFormulaTruth_inclusion {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    (hAlpha : Order.IsSuccLimit alpha) (hBeta : Order.IsSuccLimit beta)
    (truth : RankClass beta) {n : Nat} (phi : RankPredicateFormula 0 n)
    (values : Fin n → RankDomain alpha) :
    rankFormulaTruth hAlpha (truth ∘ rankInclusion hAB) phi values ↔
      rankFormulaTruth hBeta truth phi (rankInclusion hAB ∘ values) := by
  have hPair : rankInclusion hAB
      (rankOrderedPair hAlpha (rankNat hAlpha (rankSyntaxCode ⟨n, phi⟩))
        (rankAssignment hAlpha values)) =
      rankOrderedPair hBeta (rankNat hBeta (rankSyntaxCode ⟨n, phi⟩))
        (rankAssignment hBeta (rankInclusion hAB ∘ values)) := by
    apply Subtype.ext
    change ZFSet.pair _ _ = ZFSet.pair _ _
    rw [rankAssignment_inclusion_val hAB hAlpha hBeta]
    rfl
  change truth _ ↔ truth _
  rw [hPair]

/-- Agreement of two truth predicates on every finite formula and every
assignment in the smaller rank domain. -/
def RankTruthAgreement {alpha : Ordinal.{u}} (hAlpha : Order.IsSuccLimit alpha)
    (left right : RankClass alpha) : Prop :=
  ∀ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain alpha),
    rankFormulaTruth hAlpha left phi values ↔ rankFormulaTruth hAlpha right phi values

/-- One finite formula compares truth on all valid formula/assignment codes. -/
def truthAgreementMatrix : RankPredicateFormula 2 6 :=
  let body : RankPredicateFormula 2 8 :=
    .imp (rankFormulaValidAssignment 0 6 7)
      ((rankFormulaTruthHolds 0 6 7).iff (rankFormulaTruthHolds 1 6 7))
  body.all.all

theorem truthAgreementMatrix_realize {alpha : Ordinal.{u}}
    (hAlpha : Order.IsSuccLimit alpha) (hOmega : Ordinal.omega0 < alpha)
    (left right : RankClass alpha) :
    truthAgreementMatrix.Realize ![left, right] (rankSyntaxBooks hOmega) ↔
      RankTruthAgreement hAlpha left right := by
  have hRaw : truthAgreementMatrix.Realize ![left, right] (rankSyntaxBooks hOmega) ↔
      ∀ code assignment, rankAssignmentAtCode hAlpha (rankSyntaxBooks hOmega 0)
        code assignment →
        (rankTruthHolds hAlpha left code assignment ↔
          rankTruthHolds hAlpha right code assignment) := by
    simp [truthAgreementMatrix, RankPredicateFormula.Realize,
      RankPredicateFormula.realize_iff, rankFormulaValidAssignment_realize_raw hAlpha,
      rankFormulaTruthHolds_realize hAlpha, Fin.snoc]
  rw [hRaw]
  constructor
  · intro h n phi values
    exact h _ _ (rankAssignmentAtCode_formula hAlpha hOmega phi values)
  · intro h code assignment hValid
    obtain ⟨n, phi, values, rfl, rfl⟩ := (rankAssignmentAtCode_iff hAlpha hOmega _ _).mp hValid
    exact h n phi values

/-- For actual truth predicates, agreement on the smaller domain is exactly
full first-order elementarity of its natural inclusion. -/
theorem rankTruthAgreement_iff_inclusion {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    (hAlpha : Order.IsSuccLimit alpha) (hBeta : Order.IsSuccLimit beta)
    (left : RankClass alpha) (right : RankClass beta)
    (hLeft : RankTruthConditions hAlpha left) (hRight : RankTruthConditions hBeta right) :
    RankTruthAgreement hAlpha left (right ∘ rankInclusion hAB) ↔
      RankElementaryInclusion alpha beta := by
  rw [rankElementaryInclusion_iff hAB]
  constructor
  · intro h n phi values
    have hCompare := h n phi values
    rw [hLeft.realize, rankFormulaTruth_inclusion hAB hAlpha hBeta, hRight.realize] at hCompare
    exact hCompare.symm
  · intro h n phi values
    rw [hLeft.realize, rankFormulaTruth_inclusion hAB hAlpha hBeta, hRight.realize]
    exact (h n phi values).symm

end RankReflection
