import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport

/-!
# High jets of the fixed one-sided Taylor representatives

At the root circle, a fixed radial Taylor polynomial retains each
radial trace through its degree and deletes every higher radial trace.
It does not delete high angular derivatives of those retained traces.
Thus every full derivative is controlled by the same-order source jet.
The angular interpolation also uses exactly the original finite data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

theorem radialBoundaryJet_boundaryTaylorPolynomial_eq_ite
    (n : ℕ) (c : ℝ) (A : ℕ → ℝ → ℝ) (k : ℕ) (θ : ℝ) :
    radialBoundaryJet (boundaryTaylorPolynomial n c A) c k θ =
      if k ≤ n then A k θ else 0 := by
  by_cases hk : k ≤ n
  · simpa only [radialBoundaryJet, if_pos hk] using
      iteratedDeriv_boundaryTaylorPolynomial n c A hk θ
  rw [if_neg hk]
  unfold radialBoundaryJet boundaryTaylorPolynomial
  have hmono (j : ℕ) : ContDiff ℝ (k : ℕ∞ω)
      (fun x : ℝ => A j θ / (j.factorial : ℝ) * (x - c) ^ j) := by
    fun_prop
  rw [iteratedDeriv_fun_sum (fun j _ => (hmono j).contDiffAt)]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : k ≠ j := by
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    omega
  have hzero : iteratedDeriv k (fun x : ℝ => (x - c) ^ j) c = 0 := by
    have he := congrFun (iteratedDeriv_comp_sub_const k (fun x : ℝ => x ^ j) c) c
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, ite_eq_right hne,
      Nat.cast_zero] using he
  rw [iteratedDeriv_const_mul_field, hzero, mul_zero]

/-- All output orders are allowed while the representative degree
stays fixed. The zero-order identity is included but never estimated
by a bound on a real angular lift. -/
theorem norm_iteratedFDeriv_oneSidedBoundaryTaylorRepresentative_le
    {F : PolarPoint → ℝ} {a b c : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : c ∈ Icc a b) (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (n k : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ k (oneSidedBoundaryTaylorRepresentative n c F) (c, θ)‖ ≤
      (2 : ℝ) ^ k * ‖iteratedFDeriv ℝ k F (c, θ)‖ := by
  let T := oneSidedBoundaryTaylorRepresentative n c F
  have hT : ContDiff ℝ ∞ T := contDiff_oneSidedBoundaryTaylorRepresentative c hFc n
  apply norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ hT.contDiffOn
    k (mem_univ (c, θ)) (norm_nonneg _)
  intro i j hij
  rw [Real.norm_eq_abs,
    ← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      isOpen_univ hT.contDiffOn c (fun _ => mem_univ _) i j θ]
  by_cases hi : i ≤ n
  · have he : radialBoundaryJet T c i = radialBoundaryJet F c i := by
      funext η
      exact radialBoundaryJet_oneSidedBoundaryTaylorRepresentative F n c hi η
    rw [he, iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
      hab hF hc hFc i j θ]
    simpa only [hij] using
      abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
        hab hF hc (hFc θ) i j
  · have he : radialBoundaryJet T c i = (fun _ => (0 : ℝ)) := by
      funext η
      simpa only [T, oneSidedBoundaryTaylorRepresentative, if_neg hi] using
        radialBoundaryJet_boundaryTaylorPolynomial_eq_ite n c (radialBoundaryJet F c) i η
    rw [he, iteratedDeriv_fun_const_zero, abs_zero]
    exact norm_nonneg _

/-- The fixed representative changes none of the data actually used by
the angular patch. This is an equality of the displayed whole functions,
so later high-jet bounds apply to the already chosen angle. -/
theorem wholeComponentEndpointAngle_oneSidedRepresentative
    (n : ℕ) (ψ : Bool → PolarPoint → ℝ) (l r c d κ M : ℝ) :
    wholeComponentEndpointAngle n (oneSidedEndpointRepresentative (n + 2) l r ψ)
        l r c d κ M =
      positiveAngularTaylorInterpolation (n + 1) l r
        (endpointAngularWidth (n + 1) l r c d κ M) (rawEndpointAngularData l r ψ) := by
  have hpoly (side : Bool) :
      boundaryTaylorPolynomial (n + 1) (if side then r else l)
          (rawEndpointAngularData l r (oneSidedEndpointRepresentative (n + 2) l r ψ) side) =
        boundaryTaylorPolynomial (n + 1) (if side then r else l)
          (rawEndpointAngularData l r ψ side) := by
    funext p
    unfold boundaryTaylorPolynomial
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n + 2 := by
      have hjlt := Finset.mem_range.mp hj
      omega
    have he : rawEndpointAngularData l r
        (oneSidedEndpointRepresentative (n + 2) l r ψ) side j p.2 =
          rawEndpointAngularData l r ψ side j p.2 :=
      radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
        (ψ side) (n + 2) (if side then r else l) hjn p.2
    rw [he]
  funext p
  have hl := congrFun (hpoly false) p
  have hr := congrFun (hpoly true) p
  simp only [Bool.false_eq_true, ite_false, ite_true] at hl hr
  dsimp only [wholeComponentEndpointAngle, positiveAngularTaylorInterpolation,
    positiveAngularTaylorPatch]
  rw [hl, hr]

end ContinuousFlexibility.Analysis
