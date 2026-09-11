import RankReflection.FormulaRelativization
import FullMarkedBLP.RankTruthMatrixCorrectness

namespace RankReflection

open FullMarkedBLP

universe u

/-- An external class on one set-sized rank domain is represented by a
genuine set. This set is available in every strictly larger rank domain. -/
noncomputable def rankClassSet {alpha : Ordinal.{u}} (predicate : RankClass alpha) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x : RankDomain alpha, x.val = z ∧ predicate x)
    (ZFSet.vonNeumann alpha)

theorem rankClassSet_mem {alpha : Ordinal.{u}} (predicate : RankClass alpha)
    (x : RankDomain alpha) : x.val ∈ rankClassSet predicate ↔ predicate x := by
  rw [rankClassSet, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hYX, hY⟩
    exact (Subtype.ext hYX : y = x) ▸ hY
  · exact fun h => ⟨ZFSet.mem_vonNeumann.mpr x.property, x, rfl, h⟩

theorem rankClassSet_rank_le {alpha : Ordinal.{u}} (predicate : RankClass alpha) :
    (rankClassSet predicate).rank ≤ alpha := by
  have hSubset : rankClassSet predicate ⊆ ZFSet.vonNeumann alpha :=
    fun _ h => (ZFSet.mem_sep.mp h).1
  simpa only [ZFSet.rank_vonNeumann] using ZFSet.rank_mono hSubset

noncomputable def rankClassSetIn {alpha beta : Ordinal.{u}} (hAB : alpha < beta)
    (predicate : RankClass alpha) : RankDomain beta :=
  ⟨rankClassSet predicate, (rankClassSet_rank_le predicate).trans_lt hAB⟩

/-- The smaller rank domain as a set parameter of the ambient structure. -/
noncomputable def rankDomainSet {alpha beta : Ordinal.{u}} (hAB : alpha < beta) :
    RankDomain beta := ⟨ZFSet.vonNeumann alpha, by simpa only [ZFSet.rank_vonNeumann] using hAB⟩

/-- The canonical pure formula, with the original set parameters followed
by one set for each class predicate and finally the quantifier domain. -/
def setMatrix {m n : Nat} (phi : RankPredicateFormula m n) :
    RankPredicateFormula 0 (n + (m + 1)) :=
  setRelativize phi (Fin.castAdd (m + 1)) (fun a => Fin.natAdd n a.castSucc)
    (Fin.natAdd n (Fin.last m))

theorem setMatrix_realize {alpha beta : Ordinal.{u}} (hAB : alpha < beta)
    {m n : Nat} (phi : RankPredicateFormula m n)
    (predicates : Fin m → RankClass alpha) (values : Fin n → RankDomain alpha)
    (sets : Fin m → RankDomain beta)
    (hSets : ∀ a (x : RankDomain alpha), x.val ∈ (sets a).val ↔ predicates a x) :
    (setMatrix phi).Realize Fin.elim0
      (Fin.append (rankInclusion hAB.le ∘ values) (Fin.snoc sets (rankDomainSet hAB))) ↔
      phi.Realize predicates values := by
  apply setRelativize_realize hAB.le
  · intro i
    simp only [Fin.append_left, rankInclusion_val, Function.comp_apply]
  · intro a x
    simpa only [Fin.append_right, Fin.snoc_castSucc] using hSets a x
  · simp only [Fin.append_right, Fin.snoc_last, rankDomainSet]

/-- A first-order formula describing satisfaction in a smaller rank domain,
using six actual syntax books, a truth set, and the domain set. -/
def rankSetTruthFormula : RankPredicateFormula 0 8 := setMatrix rankTruthMatrix

theorem rankSetTruthFormula_realize {alpha beta : Ordinal.{u}} (hAB : alpha < beta)
    (hLimit : Order.IsSuccLimit alpha) (hOmega : Ordinal.omega0 < alpha)
    (truth : RankDomain beta) :
    rankSetTruthFormula.Realize Fin.elim0
      (Fin.append (rankInclusion hAB.le ∘ rankSyntaxBooks hOmega)
        (Fin.snoc (fun _ : Fin 1 => truth) (rankDomainSet hAB))) ↔
      RankTruthConditions hLimit (fun x => x.val ∈ truth.val) := by
  exact (setMatrix_realize hAB rankTruthMatrix
    (fun _ x => x.val ∈ truth.val) (rankSyntaxBooks hOmega) (fun _ => truth)
    (fun _ _ => Iff.rfl)).trans (rankTruthMatrix_correct hLimit hOmega _)

/-- The actual truth set is constructed by separation, and satisfies the
finite pure first-order formula in every larger rank domain. -/
theorem exists_rankSetTruth {alpha beta : Ordinal.{u}} (hAB : alpha < beta)
    (hLimit : Order.IsSuccLimit alpha) (hOmega : Ordinal.omega0 < alpha) :
    ∃ truth : RankDomain beta, rankSetTruthFormula.Realize Fin.elim0
      (Fin.append (rankInclusion hAB.le ∘ rankSyntaxBooks hOmega)
        (Fin.snoc (fun _ : Fin 1 => truth) (rankDomainSet hAB))) := by
  refine ⟨rankClassSetIn hAB (rankSatisfaction hLimit), ?_⟩
  apply (rankSetTruthFormula_realize hAB hLimit hOmega _).mpr
  have hPredicate : (fun x : RankDomain alpha =>
      x.val ∈ (rankClassSetIn hAB (rankSatisfaction hLimit)).val) =
        rankSatisfaction hLimit := by
    funext x
    exact propext (rankClassSet_mem _ x)
  rw [hPredicate]
  exact rankSatisfaction_conditions hLimit

end RankReflection
