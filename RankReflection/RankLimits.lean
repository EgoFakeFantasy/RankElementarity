import RankReflection.RankInclusion
import FullMarkedBLP.RankOmegaPreservation

namespace RankReflection

open FullMarkedBLP

universe u

def nonemptySentence : RankPredicateFormula 0 0 := (RankPredicateFormula.equal 0 0).ex

theorem nonemptySentence_realize (alpha : Ordinal.{u}) :
    nonemptySentence.Realize Fin.elim0 (Fin.elim0 : Fin 0 → RankDomain alpha) ↔ 0 < alpha := by
  simp only [nonemptySentence, RankPredicateFormula.realize_ex, RankPredicateFormula.Realize]
  constructor
  · rintro ⟨x, _⟩
    exact lt_of_le_of_lt bot_le x.property
  · exact fun h => ⟨⟨∅, by simpa only [ZFSet.rank_empty] using h⟩, trivial⟩

def hasContainerFormula : RankPredicateFormula 0 1 := (RankPredicateFormula.member 0 1).ex

theorem hasContainerFormula_realize {alpha : Ordinal.{u}} (values : Fin 1 → RankDomain alpha) :
    hasContainerFormula.Realize Fin.elim0 values ↔
      ∃ y : RankDomain alpha, (values 0).val ∈ y.val := by
  simp [hasContainerFormula, RankPredicateFormula.realize_ex, RankPredicateFormula.Realize, Fin.snoc]

def membershipClosureSentence : RankPredicateFormula 0 0 := hasContainerFormula.all

theorem membershipClosureSentence_realize (alpha : Ordinal.{u}) :
    membershipClosureSentence.Realize Fin.elim0 (Fin.elim0 : Fin 0 → RankDomain alpha) ↔
      ∀ x : RankDomain alpha, ∃ y : RankDomain alpha, x.val ∈ y.val := by
  simp [membershipClosureSentence, RankPredicateFormula.Realize, hasContainerFormula_realize, Fin.snoc]

theorem rankDomain_container {alpha : Ordinal.{u}} (hAlpha : Order.IsSuccLimit alpha) (x : RankDomain alpha) :
    ∃ y : RankDomain alpha, x.val ∈ y.val := by
  exact ⟨⟨{x.val}, by rw [ZFSet.rank_singleton]; exact hAlpha.succ_lt x.property⟩, by simp⟩

theorem isSuccLimit_of_rankDomain_container {alpha : Ordinal.{u}} (hPos : 0 < alpha)
    (hClosed : ∀ x : RankDomain alpha, ∃ y : RankDomain alpha, x.val ∈ y.val) :
    Order.IsSuccLimit alpha := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit alpha with rfl | ⟨theta, rfl⟩ | hLimit
  · exact False.elim ((lt_irrefl _) hPos)
  · let x : RankDomain (Order.succ theta) :=
      ⟨theta.toZFSet, by simpa only [Ordinal.rank_toZFSet] using Order.lt_succ theta⟩
    obtain ⟨y, hMember⟩ := hClosed x
    have hLower : theta < y.val.rank := by
      simpa only [x, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hMember
    exact False.elim (not_lt_of_ge (Order.le_of_lt_succ y.property) hLower)
  · exact hLimit

/-- A proper elementary rank inclusion has a nonzero limit source. This
handles the finite and successor cases without any cardinal assumptions. -/
theorem RankElementaryInclusion.isSuccLimit_source {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (hAB : alpha < beta) :
    Order.IsSuccLimit alpha := by
  have hPos : 0 < alpha := (nonemptySentence_realize alpha).mp
    ((hElem.map_sentence nonemptySentence).mp
      ((nonemptySentence_realize beta).mpr (lt_of_le_of_lt bot_le hAB)))
  rcases Ordinal.zero_or_succ_or_isSuccLimit alpha with rfl | ⟨theta, rfl⟩ | hLimit
  · exact False.elim ((lt_irrefl _) hPos)
  · let x : RankDomain (Order.succ theta) :=
      ⟨theta.toZFSet, by simpa only [Ordinal.rank_toZFSet] using Order.lt_succ theta⟩
    let y : RankDomain beta := ⟨ZFSet.vonNeumann (Order.succ theta), by simpa using hAB⟩
    have hTruth := hElem.map_predicateFormula hAB.le hasContainerFormula ![x]
    rw [hasContainerFormula_realize, hasContainerFormula_realize] at hTruth
    have hMember : (rankInclusion hAB.le x).val ∈ y.val :=
      ZFSet.mem_vonNeumann.mpr (by simpa only [rankInclusion_val, x, Ordinal.rank_toZFSet] using Order.lt_succ theta)
    obtain ⟨z, hXZ⟩ := hTruth.mp ⟨y, hMember⟩
    have hLower : theta < z.val.rank := by
      simpa [x] using ZFSet.rank_lt_of_mem hXZ
    exact False.elim (not_lt_of_ge (Order.le_of_lt_succ z.property) hLower)
  · exact hLimit

theorem RankElementaryInclusion.isSuccLimit_target {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (hAB : alpha < beta) :
    Order.IsSuccLimit beta := by
  have hAlpha := hElem.isSuccLimit_source hAB
  apply isSuccLimit_of_rankDomain_container (hAlpha.pos.trans hAB)
  apply (membershipClosureSentence_realize beta).mp
  apply (hElem.map_sentence membershipClosureSentence).mpr
  exact (membershipClosureSentence_realize alpha).mpr (rankDomain_container hAlpha)

def existsLimitSentence : RankPredicateFormula 0 0 :=
  ((rankPredicateOfFormula rankOrdinalFormula).and
    (rankPredicateOfFormula rankNonzeroLimitFormula)).ex

theorem existsLimitSentence_realize (alpha : Ordinal.{u}) :
    existsLimitSentence.Realize Fin.elim0 (Fin.elim0 : Fin 0 → RankDomain alpha) ↔
      Ordinal.omega0 < alpha := by
  have hVector (x : RankDomain alpha) :
      Fin.snoc (Fin.elim0 : Fin 0 → RankDomain alpha) x = ![x] := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  have hSingle (x : RankDomain alpha) :
      ((rankPredicateOfFormula rankOrdinalFormula).and
        (rankPredicateOfFormula rankNonzeroLimitFormula)).Realize Fin.elim0
          (Fin.snoc (Fin.elim0 : Fin 0 → RankDomain alpha) x) ↔
        ZFSet.IsOrdinal x.val ∧ rankIsNonzeroLimit x := by
    rw [hVector, RankPredicateFormula.realize_and, rankPredicateOfFormula_realize,
      rankPredicateOfFormula_realize]
    exact and_congr (rankOrdinalFormula_realize x) (rankNonzeroLimitFormula_realize x)
  simp only [existsLimitSentence, RankPredicateFormula.realize_ex]
  constructor
  · rintro ⟨x, h⟩
    obtain ⟨hOrdinal, hLimit⟩ := (hSingle x).mp h
    let o : OrdinalDomain alpha := ⟨x.val.rank, x.property⟩
    have hSame : ordinalDomainElement o = x := Subtype.ext hOrdinal.toZFSet_rank_eq
    rw [← hSame] at hLimit
    exact (Ordinal.omega0_le_of_isSuccLimit ((rankIsNonzeroLimit_ordinal_iff o).mp hLimit)).trans_lt
      x.property
  · intro hOmega
    refine ⟨ordinalDomainElement ⟨Ordinal.omega0, hOmega⟩, (hSingle _).mpr ?_⟩
    exact ⟨ZFSet.isOrdinal_toZFSet _,
      (rankIsNonzeroLimit_ordinal_iff (⟨Ordinal.omega0, hOmega⟩ : OrdinalDomain alpha)).mpr
        Ordinal.isSuccLimit_omega0⟩

/-- The coding tables fit in both domains of every proper elementary rank
inclusion; their smallness is derived from the original hypothesis. -/
theorem RankElementaryInclusion.omega_lt_source {alpha beta : Ordinal.{u}}
    (hElem : RankElementaryInclusion alpha beta) (hAB : alpha < beta) :
    Ordinal.omega0 < alpha := by
  have hOmegaBeta := (Ordinal.omega0_le_of_isSuccLimit (hElem.isSuccLimit_source hAB)).trans_lt hAB
  exact (existsLimitSentence_realize alpha).mp ((hElem.map_sentence existsLimitSentence).mp
    ((existsLimitSentence_realize beta).mpr hOmegaBeta))

end RankReflection
