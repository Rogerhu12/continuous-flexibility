module

public import ContinuousFlexibility.Analysis.N07aIntervalCoefficientExhaustion

/-!
# The cubic graph estimate with only open-interval coefficient smoothness

The actual weak unknown is fixed throughout. Only the coefficients are
approximated. Their genuine inset approximants retain the lower cylinder
weight and the same quantitative bounds, and dominated L² convergence
identifies the limit with the prescribed actual differential expression.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem n07a_differential_abs_bound {a da c V j K u d dd : ℝ}
    (_hK : 0 ≤ K) (ha : |a| ≤ K) (hda : |da| ≤ K)
    (hc : |c| ≤ K) (hV : |V| ≤ K) :
    |-a * dd - da * d + j ^ 2 * c * u + V * u| ≤
      K * |dd| + K * |d| + (j ^ 2 * K + K) * |u| := by
  have hs : |-a * dd - da * d| ≤ |a| * |dd| + |da| * |d| := by
    simpa only [sub_eq_add_neg, abs_mul, abs_neg] using
      abs_add_le (-a * dd) (-(da * d))
  calc
    _ ≤ (|-a * dd - da * d| + |j ^ 2 * c * u|) + |V * u| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |a| * |dd| + |da| * |d| + j ^ 2 * |c| * |u| + |V| * |u| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg j)]
      linarith
    _ ≤ K * |dd| + K * |d| + j ^ 2 * K * |u| + K * |u| := by
      gcongr
    _ = _ := by ring

private theorem n07a_L2_tendsto_of_representatives
    (u : ℕ → N07aIntervalL2) (v : N07aIntervalL2)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hu : ∀ n, (u n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f n)
    (hv : (v : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g)
    {B : ℝ → ℝ} (hB : MemLp B 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hb : ∀ n, ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), |f n x - g x| ≤ B x)
    (ht : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto u atTop (𝓝 v) := by
  have hf (n : ℕ) : MemLp (f n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (memLp_congr_ae (hu n)).mp (Lp.memLp (u n))
  have hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (memLp_congr_ae hv).mp (Lp.memLp v)
  have he (n : ℕ) : (hf n).toLp (f n) = u n :=
    Lp.ext ((hf n).coeFn_toLp.trans (hu n).symm)
  have hev : hg.toLp g = v := Lp.ext (hg.coeFn_toLp.trans hv.symm)
  have h := spaces_tendsto_toLp_of_dominated hf hg hB (Eventually.of_forall hb) ht
  simpa only [he, hev] using h

/-- Actual open-interval coefficients suffice for the original uniform
energy estimate. The extra upper bound on `c` is a primitive value bound,
used only in dominated convergence of the actual forcing classes. -/
theorem n07a_open_weak_cubic_graph_bound {a c V q : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1))
    (hc : ContDiffOn ℝ ∞ c (Ioo (0 : ℝ) 1))
    (hV : ContDiffOn ℝ ∞ V (Ioo (0 : ℝ) 1))
    (hq : ContDiffOn ℝ ∞ q (Ioo (0 : ℝ) 1)) (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Ioo (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Ioo (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Ioo (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Ioo (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hc₂ : ∀ y ∈ Ioo (0 : ℝ) 1, |c y| ≤ K)
    (hV₁ : ∀ y ∈ Ioo (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Ioo (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Ioo (0 : ℝ) 1, |deriv (deriv q) y| ≤ K)
    (u d dd F : N07aIntervalL2)
    (hud : HasIntervalWeakDerivative 0 1 u d)
    (hdd : HasIntervalWeakDerivative 0 1 d dd)
    (hF : (F : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => -a x * dd x - deriv a x * d x + j ^ 2 * c x * u x + V x * u x)) :
    n07aCylinderEnergy j u d dd ≤ 16384 * K ^ 10 * (‖F‖ ^ 2 + ‖u‖ ^ 2) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have haabs (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |a x| ≤ K := by
    rw [abs_of_nonneg ((one_div_nonneg.mpr hK₀).trans (ha₁ x hx))]
    exact ha₂ x hx
  let A : ℕ → ℝ → ℝ := fun n => n07aIntervalCoeffApprox n a
  let C : ℕ → ℝ → ℝ := fun n => n07aIntervalCoeffApprox n c
  let W : ℕ → ℝ → ℝ := fun n => n07aIntervalCoeffApprox n V
  let Q : ℕ → ℝ → ℝ := fun n => n07aIntervalCoeffApprox n q
  have hA (n : ℕ) : ContDiff ℝ ∞ (A n) := n07aIntervalCoeffApprox_contDiff n ha
  have hC (n : ℕ) : ContDiff ℝ ∞ (C n) := n07aIntervalCoeffApprox_contDiff n hc
  have hW (n : ℕ) : ContDiff ℝ ∞ (W n) := n07aIntervalCoeffApprox_contDiff n hV
  have hQ (n : ℕ) : ContDiff ℝ ∞ (Q n) := n07aIntervalCoeffApprox_contDiff n hq
  have hAder (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |deriv (A n) x| ≤ K := by
    rw [n07aIntervalCoeffApprox_deriv n ha hx, abs_mul,
      abs_of_nonneg (n07aIntervalInsetSlope_bounds n).1]
    exact (mul_le_mul_of_nonneg_right (ha₃ _ (n07aIntervalInset_mem n hx))
      (n07aIntervalInsetSlope_bounds n).1).trans
        (mul_le_of_le_one_right hK₀ (n07aIntervalInsetSlope_bounds n).2)
  have hQder (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      |deriv (deriv (Q n)) x| ≤ K := by
    rw [n07aIntervalCoeffApprox_second n hq hx, abs_mul,
      abs_of_nonneg (sq_nonneg (n07aIntervalInsetSlope n))]
    have hs : n07aIntervalInsetSlope n ^ 2 ≤ 1 := by
      nlinarith [(n07aIntervalInsetSlope_bounds n).1, (n07aIntervalInsetSlope_bounds n).2]
    exact (mul_le_mul_of_nonneg_right (hq₂ _ (n07aIntervalInset_mem n hx))
      (sq_nonneg _)).trans (mul_le_of_le_one_right hK₀ hs)
  let Fn : ℕ → N07aIntervalL2 := fun n =>
    n07aIntervalDifferential (A n) (C n) (W n) ((hA n).of_le (by simp))
      (hC n).continuous (hW n).continuous j u d dd
  have hbound (n : ℕ) : n07aCylinderEnergy j u d dd ≤
      16384 * K ^ 10 * (‖Fn n‖ ^ 2 + ‖u‖ ^ 2) := by
    apply n07a_weak_cubic_graph_bound ((hA n).of_le (by simp)) (hC n).continuous
      (hW n).continuous ((hQ n).of_le (by simp)) hK
      (fun x hx => ?_) (fun x hx => ?_) (hAder n) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_) (hQder n) u d dd hud hdd
    · dsimp only [A]
      rw [n07aIntervalCoeffApprox_eq n a hx]
      exact ha₁ _ (n07aIntervalInset_mem n hx)
    · dsimp only [A]
      rw [n07aIntervalCoeffApprox_eq n a hx]
      exact ha₂ _ (n07aIntervalInset_mem n hx)
    · dsimp only [C]
      rw [n07aIntervalCoeffApprox_eq n c hx]
      exact (div_le_div_of_nonneg_right (n07aIntervalInset_weight_le n x) hK₀).trans
        (hc₁ _ (n07aIntervalInset_mem n hx))
    · dsimp only [W]
      rw [n07aIntervalCoeffApprox_eq n V hx]
      exact hV₁ _ (n07aIntervalInset_mem n hx)
    · dsimp only [C, A, Q]
      rw [n07aIntervalCoeffApprox_eq n c hx, n07aIntervalCoeffApprox_eq n a hx,
        n07aIntervalCoeffApprox_eq n q hx]
      exact hqa _ (n07aIntervalInset_mem n hx)
  let f : ℕ → ℝ → ℝ := fun n x =>
    -A n x * dd x - deriv (A n) x * d x + j ^ 2 * C n x * u x + W n x * u x
  let g : ℝ → ℝ := fun x =>
    -a x * dd x - deriv a x * d x + j ^ 2 * c x * u x + V x * u x
  let B : ℝ → ℝ := fun x =>
    K * |dd x| + K * |d x| + (j ^ 2 * K + K) * |u x|
  have hB : MemLp B 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hm := (((Lp.memLp dd).norm.const_mul K).add ((Lp.memLp d).norm.const_mul K)).add
      ((Lp.memLp u).norm.const_mul (j ^ 2 * K + K))
    apply (memLp_congr_ae ?_).mp hm
    exact Eventually.of_forall fun x => by
      simp only [Pi.add_apply, Real.norm_eq_abs, B]
  have hfbound (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |f n x| ≤ B x := by
    apply n07a_differential_abs_bound hK₀
    · dsimp only [A]
      rw [n07aIntervalCoeffApprox_eq n a (Ioo_subset_Icc_self hx)]
      exact haabs _ (n07aIntervalInset_mem n (Ioo_subset_Icc_self hx))
    · exact hAder n x (Ioo_subset_Icc_self hx)
    · dsimp only [C]
      rw [n07aIntervalCoeffApprox_eq n c (Ioo_subset_Icc_self hx)]
      exact hc₂ _ (n07aIntervalInset_mem n (Ioo_subset_Icc_self hx))
    · dsimp only [W]
      rw [n07aIntervalCoeffApprox_eq n V (Ioo_subset_Icc_self hx)]
      exact hV₁ _ (n07aIntervalInset_mem n (Ioo_subset_Icc_self hx))
  have hgbound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |g x| ≤ B x :=
    n07a_differential_abs_bound hK₀ (haabs x hx) (ha₃ x hx) (hc₂ x hx) (hV₁ x hx)
  have hFn : Tendsto Fn atTop (𝓝 F) := by
    apply n07a_L2_tendsto_of_representatives Fn F f g
      (fun n => n07aIntervalDifferential_ae _ _ _ _ _ _ _ _ _ _) hF (hB.const_mul 2)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      calc
        |f n x - g x| ≤ |f n x| + |g x| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f n x) (-g x)
        _ ≤ B x + B x := add_le_add (hfbound n x hx) (hgbound x hx)
        _ = 2 * B x := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (((((n07aIntervalCoeffApprox_tendsto ha.continuousOn hx).neg.mul_const (dd x)).sub
        ((n07aIntervalCoeffApprox_deriv_tendsto ha hx).mul_const (d x))).add
        (((n07aIntervalCoeffApprox_tendsto hc.continuousOn hx).const_mul (j ^ 2)).mul_const (u x))).add
        ((n07aIntervalCoeffApprox_tendsto hV.continuousOn hx).mul_const (u x)))
  exact ge_of_tendsto (((hFn.norm.pow 2).add_const (‖u‖ ^ 2)).const_mul (16384 * K ^ 10))
    (Eventually.of_forall hbound)

end ContinuousFlexibility.Analysis
