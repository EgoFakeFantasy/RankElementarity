import RankReflection.ElementaryInclusionFormula
import FullMarkedBLP.RankHierarchyRecursion

/-! A finite formula for the cumulative hierarchy built from recursion graphs, whose witnesses are
exactly the actual `V_delta`. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- The atom "`x` is an ordinal". -/
def ordinalAtom {m n : Nat} (x : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankOrdinalFormula ![x]

/-- Semantics of `ordinalAtom`. -/
theorem ordinalAtom_realize {eta : Ordinal.{u}} {m n : Nat} (x : Fin n)
    (classes : Fin m → RankClass eta) (values : Fin n → RankDomain eta) :
    (ordinalAtom x).Realize classes values ↔ ZFSet.IsOrdinal (values x).val := by
  rw [ordinalAtom, rankPredicateAtom_realize, rankMapSingle]
  exact rankOrdinalFormula_realize _

/-- The atom "`x` is a nonzero limit ordinal". -/
def limitAtom {m n : Nat} (x : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankNonzeroLimitFormula ![x]

/-- Semantics of `limitAtom`. -/
theorem limitAtom_realize {eta : Ordinal.{u}} {m n : Nat} (x : Fin n)
    (classes : Fin m → RankClass eta) (values : Fin n → RankDomain eta) :
    (limitAtom x).Realize classes values ↔ rankIsNonzeroLimit (values x) := by
  rw [limitAtom, rankPredicateAtom_realize, rankMapSingle]
  exact rankNonzeroLimitFormula_realize _

/-- The atom "`graph` satisfies the cumulative-hierarchy recursion". -/
def hierarchyRecAtom {m n : Nat} (graph : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankHierarchyRecFormula ![graph]

/-- Semantics of `hierarchyRecAtom`. -/
theorem hierarchyRecAtom_realize {eta : Ordinal.{u}} {m n : Nat} (graph : Fin n)
    (classes : Fin m → RankClass eta) (values : Fin n → RankDomain eta) :
    (hierarchyRecAtom graph).Realize classes values ↔ RankHierarchyRec (values graph) := by
  rw [hierarchyRecAtom, rankPredicateAtom_realize, rankMapSingle]
  exact rankHierarchyRecFormula_realize _

/-- The graph witnesses have an ordinal domain extending the index. Their
recursive values are uniquely the actual cumulative hierarchy. -/
def hierarchyFormula : RankPredicateFormula 0 2 :=
  -- Slots: 0 = index, 1 = value; quantified: 2 = upper, 3 = range, 4 = graph.
  let body : RankPredicateFormula 0 5 :=
    (ordinalAtom 2).and ((RankPredicateFormula.member 0 2).and ((rankFormulaFunction 4 2 3).and
      ((hierarchyRecAtom 4).and (rankFormulaGraphApplies 4 0 1))))
  (ordinalAtom 0).and body.ex.ex.ex

/-- `hierarchyFormula` unfolded into its witnesses, before identifying the value with `V_delta`. -/
theorem hierarchyFormula_realize_raw {eta : Ordinal.{u}} (values : Fin 2 → RankDomain eta) :
    hierarchyFormula.Realize Fin.elim0 values ↔
      ZFSet.IsOrdinal (values 0).val ∧ ∃ upper range graph : RankDomain eta,
        ZFSet.IsOrdinal upper.val ∧ (values 0).val ∈ upper.val ∧
        rankIsFunction graph upper range ∧ RankHierarchyRec graph ∧
        rankGraphApplies graph (values 0) (values 1) := by
  simp [hierarchyFormula, RankPredicateFormula.realize_and, RankPredicateFormula.realize_ex,
    RankPredicateFormula.Realize, ordinalAtom_realize, rankFormulaFunction_realize,
    hierarchyRecAtom_realize, rankFormulaGraphApplies_realize, Fin.snoc]

/-- Internal hierarchy witnesses denote exactly the ambient, actual V_delta.
Only the explicitly stated limit closure is used, not a model-of-ZFC premise. -/
theorem hierarchyFormula_realize {eta : Ordinal.{u}} (hEta : Order.IsSuccLimit eta)
    (values : Fin 2 → RankDomain eta) :
    hierarchyFormula.Realize Fin.elim0 values ↔
      ZFSet.IsOrdinal (values 0).val ∧
        (values 1).val = ZFSet.vonNeumann (values 0).val.rank := by
  rw [hierarchyFormula_realize_raw]
  constructor
  · rintro ⟨hOrdinal, upper, range, graph, hUpper, hMember, hFunction, hRec, hAt⟩
    let level : OrdinalDomain eta := ⟨(values 0).val.rank, (values 0).property⟩
    have hSame : ordinalDomainElement level = values 0 := Subtype.ext hOrdinal.toZFSet_rank_eq
    rw [← hSame] at hMember hAt
    have hValue := rankHierarchyRec_unique hFunction hUpper hRec level (values 1) hMember hAt
    exact ⟨hOrdinal, congrArg Subtype.val hValue⟩
  · rintro ⟨hOrdinal, hValue⟩
    let level : OrdinalDomain eta := ⟨(values 0).val.rank, (values 0).property⟩
    let upper : OrdinalDomain eta := ⟨Order.succ level.val, hEta.succ_lt level.property⟩
    have hBelow : level < upper := Order.lt_succ level.val
    have hSame : ordinalDomainElement level = values 0 := Subtype.ext hOrdinal.toZFSet_rank_eq
    have hValueEq : values 1 = rankHierarchy level := Subtype.ext hValue
    refine ⟨hOrdinal, ordinalDomainElement upper, rankHierarchy upper,
      rankHierarchyGraph hEta upper, ZFSet.isOrdinal_toZFSet _, ?_,
      rankHierarchyGraph_isFunction hEta upper, rankHierarchyGraph_recursion hEta upper, ?_⟩
    · rw [← hSame]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hBelow
    · rw [← hSame, hValueEq]
      exact rankHierarchyGraph_at hEta hBelow

end RankReflection
