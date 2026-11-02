import RankReflection.HierarchyFormula
import RankReflection.RankLimits
import FullMarkedBLP.RankFormulaRelabel

/-! The single existence formula that is reflected from `V_gamma` down to `V_beta`, and its raw
unfolding. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- Positions of the arguments of `elementaryInclusionFormula` inside the eleven slots of
`reflectionBody`: the six books, `V_alpha` and the witness domain. -/
def reflectionElementaryIndices : Fin 8 → Fin 11 := Fin.append (Fin.castAdd 5) ![6, 10]

/-- Body of `reflectionFormula`. Slots 0–5 are the syntax books, 6 is `V_alpha`, 7 is `alpha` and 8
the lower bound; the two quantified slots are 9, the witness height `delta`, and 10, its domain. It
says `alpha, bound ∈ delta`, `delta` is a nonzero limit, slot 10 is `V_delta`, and `V_alpha ≺
V_delta`. -/
def reflectionBody : RankPredicateFormula 0 11 :=
  (RankPredicateFormula.member 7 9).and ((RankPredicateFormula.member 8 9).and
    ((limitAtom 9).and ((hierarchyFormula.relabelSets ![9, 10]).and
      (elementaryInclusionFormula.relabelSets reflectionElementaryIndices))))

/-- One first-order existence statement. Free parameters are the six syntax
books, V_alpha, alpha, and the prescribed lower bound. -/
def reflectionFormula : RankPredicateFormula 0 9 := reflectionBody.ex.ex

/-- The arguments passed to `elementaryInclusionFormula`, given the outer parameters and the witness
domain. -/
def reflectionElementaryValues {X : Type*} (outer : Fin 9 → X) (domain : X) : Fin 8 → X :=
  Fin.append (fun i : Fin 6 => outer (i.castAdd 3)) ![outer 6, domain]

/-- `reflectionElementaryIndices` selects exactly `reflectionElementaryValues`. -/
theorem reflectionElementaryValues_eq {X : Type*} (outer : Fin 9 → X) (index domain : X) :
    (Fin.snoc (Fin.snoc outer index) domain : Fin 11 → X) ∘ reflectionElementaryIndices =
      reflectionElementaryValues outer domain := by
  funext i
  fin_cases i <;> rfl

/-- Semantics of `reflectionBody`, slot by slot. -/
theorem reflectionBody_realize {eta : Ordinal.{u}} (outer : Fin 11 → RankDomain eta) :
    reflectionBody.Realize Fin.elim0 outer ↔
      (outer 7).val ∈ (outer 9).val ∧ (outer 8).val ∈ (outer 9).val ∧
      rankIsNonzeroLimit (outer 9) ∧
      hierarchyFormula.Realize Fin.elim0 (outer ∘ ![9, 10]) ∧
      elementaryInclusionFormula.Realize Fin.elim0 (outer ∘ reflectionElementaryIndices) := by
  simp only [reflectionBody, RankPredicateFormula.realize_and, limitAtom_realize,
    RankPredicateFormula.realize_relabelSets]
  rfl

/-- `reflectionFormula` unfolded into explicit witnesses `index` and `domain`. -/
theorem reflectionFormula_realize_raw {eta : Ordinal.{u}} (outer : Fin 9 → RankDomain eta) :
    reflectionFormula.Realize Fin.elim0 outer ↔
      ∃ index domain : RankDomain eta,
        (outer 7).val ∈ index.val ∧ (outer 8).val ∈ index.val ∧ rankIsNonzeroLimit index ∧
        hierarchyFormula.Realize Fin.elim0 ![index, domain] ∧
        elementaryInclusionFormula.Realize Fin.elim0 (reflectionElementaryValues outer domain) := by
  simp only [reflectionFormula, RankPredicateFormula.realize_ex]
  apply exists_congr
  intro index
  apply exists_congr
  intro domain
  rw [reflectionBody_realize, reflectionElementaryValues_eq, rankMapPair]
  simp [Fin.snoc]

end RankReflection
