import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets
import ContinuousFlexibility.Analysis.RootCompositionZeroOrder
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Ordinary root jets at the boundary

For a negative real argument the real three-halves power is zero. Thus
the odd root quotient vanishes on the negative half-plane, while the even
root average agrees there with the smooth zero-section restriction of
its input. The one-sided comparison lemmas then bound the ordinary jets
that occur in `CSBound`, including when the root formulas are not smooth
across the boundary as functions on the whole plane.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Mathlib's real three-halves power vanishes on the nonpositive axis. -/
theorem rpow_three_halves_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    x ^ (3 / 2 : ℝ) = 0 := by
  rcases hx.eq_or_lt with hx | hx
  · rw [hx]
    exact Real.zero_rpow (by norm_num)
  · rw [Real.rpow_def_of_neg hx,
      show (3 / 2 : ℝ) * Real.pi = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]

/-- On the nonpositive half-plane the even formula is the zero-section
restriction of its input. -/
theorem rootEven_eq_zero_section_of_nonpos (G : ℝ × ℝ × ℝ → ℝ)
    {p : PolarPoint} (hp : p.1 ≤ 0) :
    rootEven G p = G (p.1, 0, p.2) := by
  rw [rootEven, rpow_three_halves_eq_zero_of_nonpos hp, neg_zero]
  ring

/-- On the negative half-plane the odd formula vanishes by total division. -/
theorem rootOdd_eq_zero_of_neg (G : ℝ × ℝ × ℝ → ℝ)
    {p : PolarPoint} (hp : p.1 < 0) : rootOdd G p = 0 := by
  simp only [rootOdd, ite_eq_right (ne_of_lt hp),
    rpow_three_halves_eq_zero_of_nonpos hp.le, neg_zero, sub_self, mul_zero, div_zero]

/-- Every ordinary positive-order odd jet at the boundary is zero,
without any regularity hypothesis on the input. -/
theorem iteratedFDeriv_rootOdd_succ_zero (G : ℝ × ℝ × ℝ → ℝ)
    (n : ℕ) (θ : ℝ) :
    iteratedFDeriv ℝ (n + 1) (rootOdd G) (0, θ) = 0 :=
  iteratedFDeriv_succ_eq_zero_at_zero_of_eqOn_neg_zero
    (fun _ hp => rootOdd_eq_zero_of_neg G hp) n θ

/-- The norm-one linear embedding of the zero section in the source space. -/
def rootZeroCoordinate : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp]
theorem rootZeroCoordinate_apply (p : ℝ × ℝ) :
    rootZeroCoordinate p = (p.1, 0, p.2) := rfl

@[simp]
theorem norm_rootZeroCoordinate : ‖rootZeroCoordinate‖ = 1 := by
  simp [rootZeroCoordinate, ContinuousLinearMap.opNorm_prod, Prod.norm_mk]

/-- Restriction to the zero section does not increase any smooth jet norm. -/
theorem norm_iteratedFDeriv_zero_section_le {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ => G (q.1, 0, q.2)) p‖ ≤
      ‖iteratedFDeriv ℝ n G (p.1, 0, p.2)‖ := by
  change ‖iteratedFDeriv ℝ n (G ∘ rootZeroCoordinate) p‖ ≤ _
  rw [rootZeroCoordinate.iteratedFDeriv_comp_right hG p (by simp)]
  simpa only [norm_rootZeroCoordinate, Finset.prod_const_one, mul_one,
    rootZeroCoordinate_apply] using
    (iteratedFDeriv ℝ n G (rootZeroCoordinate p)).norm_compContinuousLinearMap_le
      (fun _ => rootZeroCoordinate)

/-- All ordinary even boundary jets, including order zero, are bounded
by the matching input jet at the zero section. -/
theorem norm_iteratedFDeriv_rootEven_zero_le {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ n (rootEven G) (0, θ)‖ ≤
      ‖iteratedFDeriv ℝ n G (0, 0, θ)‖ := by
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero, rootEven_zero, le_rfl]
  | succ n =>
    have hsmooth : ContDiff ℝ ∞ (fun q : ℝ × ℝ => G (q.1, 0, q.2)) :=
      hG.comp rootZeroCoordinate.contDiff
    have hcompare := norm_iteratedFDeriv_succ_le_at_zero_of_eqOn_neg
      (fun p hp => rootEven_eq_zero_section_of_nonpos G hp.le) hsmooth n θ
    exact hcompare.trans (norm_iteratedFDeriv_zero_section_le hG (n + 1) (0, θ))

end ContinuousFlexibility.Analysis
