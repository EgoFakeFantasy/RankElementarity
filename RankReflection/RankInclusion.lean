import FullMarkedBLP.RankPredicatePureFormula

namespace RankReflection

open FullMarkedBLP FirstOrder

universe u

/-- Full first-order elementarity of the natural inclusion of actual rank
domains. The underlying map fixes each set, not merely its isomorphism type. -/
def RankElementaryInclusion (alpha beta : Ordinal.{u}) : Prop :=
  ∃ j : Language.ElementaryEmbedding membershipLanguage (RankDomain alpha) (RankDomain beta),
    ∀ x : RankDomain alpha, (j x).val = x.val

/-- The natural map between rank domains. -/
def rankInclusion {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta) :
    RankDomain alpha → RankDomain beta :=
  fun x => ⟨x.val, x.property.trans_le hAB⟩

@[simp]
theorem rankInclusion_val {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    (x : RankDomain alpha) : (rankInclusion hAB x).val = x.val := rfl

theorem rankInclusion_injective {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta) :
    Function.Injective (rankInclusion hAB) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : RankDomain beta => z.val) h)

theorem RankElementaryInclusion.refl (alpha : Ordinal.{u}) :
    RankElementaryInclusion alpha alpha :=
  ⟨Language.ElementaryEmbedding.refl membershipLanguage (RankDomain alpha), fun _ => rfl⟩

theorem RankElementaryInclusion.trans {alpha beta gamma : Ordinal.{u}}
    (hElemAB : RankElementaryInclusion alpha beta)
    (hElemBC : RankElementaryInclusion beta gamma) :
    RankElementaryInclusion alpha gamma := by
  obtain ⟨j, hJ⟩ := hElemAB
  obtain ⟨k, hK⟩ := hElemBC
  exact ⟨k.comp j, fun x => (hK (j x)).trans (hJ x)⟩

theorem RankElementaryInclusion.le {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) : alpha ≤ beta := by
  by_contra h
  have hBA : beta < alpha := lt_of_not_ge h
  let x : RankDomain alpha := ⟨ZFSet.vonNeumann beta, by simpa using hBA⟩
  obtain ⟨j, hJ⟩ := hElem
  have hx := (j x).property
  rw [hJ x] at hx
  simp [x] at hx

theorem RankElementaryInclusion.map_formula {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (hAB : alpha ≤ beta)
    {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (values : Fin n → RankDomain alpha) :
    phi.Realize (rankInclusion hAB ∘ values) ↔ phi.Realize values := by
  obtain ⟨j, hJ⟩ := hElem
  have hMap : (j : RankDomain alpha → RankDomain beta) = rankInclusion hAB := by
    funext x
    exact Subtype.ext (hJ x)
  simpa only [hMap] using j.map_formula phi values

theorem RankElementaryInclusion.map_predicateFormula {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (hAB : alpha ≤ beta)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain alpha) :
    phi.Realize Fin.elim0 (rankInclusion hAB ∘ values) ↔ phi.Realize Fin.elim0 values := by
  rw [rankPredicateToFormula_realize, rankPredicateToFormula_realize]
  exact hElem.map_formula hAB _ values

theorem rankElementaryInclusion_iff {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta) :
    RankElementaryInclusion alpha beta ↔
      ∀ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain alpha),
        phi.Realize Fin.elim0 (rankInclusion hAB ∘ values) ↔
          phi.Realize Fin.elim0 values := by
  constructor
  · exact fun h _ phi values => h.map_predicateFormula hAB phi values
  · intro h
    refine ⟨⟨rankInclusion hAB, ?_⟩, fun _ => rfl⟩
    intro n phi values
    simpa only [rankPredicateOfFormula_realize] using
      h n (rankPredicateOfFormula phi) values

theorem RankElementaryInclusion.map_sentence {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (phi : RankPredicateFormula 0 0) :
    phi.Realize Fin.elim0 (Fin.elim0 : Fin 0 → RankDomain beta) ↔
      phi.Realize Fin.elim0 (Fin.elim0 : Fin 0 → RankDomain alpha) := by
  have h := hElem.map_predicateFormula hElem.le phi Fin.elim0
  have hEmpty : rankInclusion hElem.le ∘ (Fin.elim0 : Fin 0 → RankDomain alpha) = Fin.elim0 :=
    Subsingleton.elim _ _
  rwa [hEmpty] at h

end RankReflection
