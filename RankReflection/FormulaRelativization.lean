import RankReflection.RankInclusion

/-! Relativization of finite formulas: class predicates become membership in set parameters, and
every quantifier is bounded by a domain set. -/

namespace RankReflection

open FullMarkedBLP

universe u

/-- Replace class predicates by membership in set parameters and restrict
every quantifier to the set named by `domain`. The result is pure finite
first-order syntax, with no external satisfaction predicate added. -/
def setRelativize {m n k : Nat} (phi : RankPredicateFormula m n)
    (vars : Fin n → Fin k) (classes : Fin m → Fin k) (domain : Fin k) :
    RankPredicateFormula 0 k :=
  match phi with
  | .falsum => .falsum
  | .equal x y => .equal (vars x) (vars y)
  | .member x y => .member (vars x) (vars y)
  | .predicate a x => .member (vars x) (classes a)
  | .imp p q => .imp (setRelativize p vars classes domain)
      (setRelativize q vars classes domain)
  | .all p => .all (.imp (.member (Fin.last k) domain.castSucc)
      (setRelativize p (Fin.lastCases (Fin.last k) (fun i => (vars i).castSucc))
        (fun a => (classes a).castSucc) domain.castSucc))

/-- Relativization exactly computes satisfaction in the smaller actual rank
domain. Set parameters for class predicates only need to agree on that domain. -/
theorem setRelativize_realize {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    {m n k : Nat} (phi : RankPredicateFormula m n)
    (vars : Fin n → Fin k) (classes : Fin m → Fin k) (domain : Fin k)
    (predicates : Fin m → RankClass alpha) (values : Fin n → RankDomain alpha)
    (outer : Fin k → RankDomain beta)
    (hVars : ∀ i, (outer (vars i)).val = (values i).val)
    (hClasses : ∀ a (x : RankDomain alpha),
      x.val ∈ (outer (classes a)).val ↔ predicates a x)
    (hDomain : (outer domain).val = ZFSet.vonNeumann alpha) :
    (setRelativize phi vars classes domain).Realize Fin.elim0 outer ↔
      phi.Realize predicates values := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change (outer (vars x) = outer (vars y)) ↔ values x = values y
    simp only [Subtype.ext_iff, hVars]
  | member x y =>
    change (outer (vars x)).val ∈ (outer (vars y)).val ↔ (values x).val ∈ (values y).val
    rw [hVars, hVars]
  | predicate a x =>
    change (outer (vars x)).val ∈ (outer (classes a)).val ↔ predicates a (values x)
    rw [hVars]
    exact hClasses a (values x)
  | imp p q ihp ihq =>
    exact imp_congr (ihp vars classes domain values outer hVars hClasses hDomain)
      (ihq vars classes domain values outer hVars hClasses hDomain)
  | @all n p ih =>
    simp only [setRelativize, RankPredicateFormula.Realize, Fin.snoc_last, Fin.snoc_castSucc]
    change (∀ x : RankDomain beta, x.val ∈ (outer domain).val →
      (setRelativize p (Fin.lastCases (Fin.last k) (fun i => (vars i).castSucc))
        (fun a => (classes a).castSucc) domain.castSucc).Realize Fin.elim0
          (Fin.snoc outer x)) ↔
      ∀ x : RankDomain alpha, p.Realize predicates (Fin.snoc values x)
    have hBody (x : RankDomain beta) (y : RankDomain alpha) (hXY : x.val = y.val) :
        (setRelativize p (Fin.lastCases (Fin.last k) (fun i => (vars i).castSucc))
          (fun a => (classes a).castSucc) domain.castSucc).Realize Fin.elim0
            (Fin.snoc outer x) ↔ p.Realize predicates (Fin.snoc values y) := by
      apply ih _ _ _ (Fin.snoc values y) (Fin.snoc outer x)
      · intro i
        cases i using Fin.lastCases with
        | last => simpa only [Fin.lastCases_last, Fin.snoc_last] using hXY
        | cast i => simpa only [Fin.lastCases_castSucc, Fin.snoc_castSucc] using hVars i
      · intro a z
        simpa only [Fin.snoc_castSucc] using hClasses a z
      · simpa only [Fin.snoc_castSucc] using hDomain
    constructor
    · intro h y
      apply (hBody (rankInclusion hAB y) y rfl).mp
      apply h
      rw [hDomain]
      exact ZFSet.mem_vonNeumann.mpr y.property
    · intro h x hx
      have hRank : x.val.rank < alpha := ZFSet.mem_vonNeumann.mp (hDomain ▸ hx)
      exact (hBody x ⟨x.val, hRank⟩ rfl).mpr (h ⟨x.val, hRank⟩)

end RankReflection
