import ContinuousFlexibility.Analysis.N06CanonicalCutoffLp
import ContinuousFlexibility.Analysis.N06CubicCutoffCommutator
import ContinuousFlexibility.Analysis.N06CylinderLp
import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier

/-!
# Strong L² convergence of the genuine cubic test operator

The divided coefficients are smooth only on the open cylinder. Their
bounded first derivatives and the cubic endpoint factor suffice for the
actual operator on a closed-cylinder smooth test to belong to the
original canonical L² space. The true cutoff commutator tends to zero
there, at the rate supplied by the weighted cutoff derivative bounds.
No extension of the coefficients through an endpoint is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

private theorem cubic_test_contDiffOn
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m)) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞
      (divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ)
      (canonicalOpen S K m) := by
  have hd : ContDiff ℝ ∞ (fun p : PolarPoint => cylinderWeight p.1 ^ 3) := by
    change ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 * (1 - p.1)) ^ 3)
    exact (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3
  have hφr : ContDiffOn ℝ ∞ (radialPartial φ) (canonicalOpen S K m) :=
    (contDiff_cylinder_radialPartial hφ).contDiffOn
  have hφt : ContDiffOn ℝ ∞ (angularPartial φ) (canonicalOpen S K m) :=
    (contDiff_cylinder_angularPartial hφ).contDiffOn
  have hR := ((hd.contDiffOn.mul hA).mul hφr).add ((hd.contDiffOn.mul hB).mul hφt)
  have hT := ((hd.contDiffOn.mul hB).mul hφr).add ((hd.contDiffOn.mul hC).mul hφt)
  exact (scalar_contDiffOn_radialPartial (isOpen_Ioo.prod isOpen_univ) hR).add
    (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hT)

/-- Bounded actual first coefficient jets give L² membership for the
actual cubic operator on every globally smooth test. The test may be
nonzero at both radial endpoints. -/
theorem n06_cubic_closedTest_memLp
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (hφ : ContDiff ℝ ∞ φ) :
    MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ) 2
      (canonicalMeasure S K m) := by
  have hμ : canonicalMeasure S K m = cylinderWindowMeasure 0 := by
    rw [canonicalMeasure, hl, hr, n06_unitCanonicalMeasure_eq_window]
  have hgraph (i : Fin 5) :
      MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) φ i) 2
        (canonicalMeasure S K m) := by
    rw [hμ]
    exact n06_cubicGraphFields_memLp hφ i
  have hmeas := n06_canonical_aestronglyMeasurable_of_continuousOn
    (cubic_test_contDiffOn hA hB hC hφ).continuousOn
  obtain ⟨hL, _, _⟩ := n06_memLp_of_square_le_finiteSum
    (n06CubicGraphFields (fun p => cylinderWeight p.1) φ)
    (K := 125 * δ ^ 2) (by positivity) hmeas hgraph (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
      have hpr : p.1 ∈ Icc (0 : ℝ) 1 := by
        simpa only [hl, hr] using Ioo_subset_Icc_self hp.1
      obtain ⟨hA₀, hB₀, hC₀, hAr, hBt, hBr, hCt⟩ := hjet p hpU
      have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
      have hd₁ := (cylinderWeight_hasDerivAt p.1).differentiableAt
      have hd : DifferentiableAt ℝ (fun q : PolarPoint => cylinderWeight q.1) p :=
        hd₁.comp p differentiableAt_fst
      have hdθ : angularPartial (fun q : PolarPoint => cylinderWeight q.1) p = 0 :=
        angularPartial_radialHeightField hd₁
      have hdr : |radialPartial (fun q : PolarPoint => cylinderWeight q.1) p| ≤ 1 := by
        change |radialPartial (radialHeightField cylinderWeight) p| ≤ 1
        rw [radialPartial_radialHeightField hd₁, (cylinderWeight_hasDerivAt p.1).deriv]
        exact abs_le.mpr ⟨by linarith [hpr.2], by linarith [hpr.1]⟩
      rw [n06CubicGraphFields_square_sum _ _ _ (cylinderWeight_nonneg hpr)]
      exact n06CubicCoefficients_divergence_sq_le hd
        ((hA.contDiffAt hn).differentiableAt (by simp))
        ((hB.contDiffAt hn).differentiableAt (by simp))
        ((hC.contDiffAt hn).differentiableAt (by simp))
        (hφ.contDiffAt.of_le (by norm_num)) hdθ
        (cylinderWeight_nonneg hpr) (cylinderWeight_le_one hpr) hdr hδ
        hA₀ hB₀ hC₀ hAr hBt hBr hCt)
  exact hL

private theorem test_first_jets_bounded {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) Real.pi,
      |φ p| ≤ J ∧ |radialPartial φ p| ≤ J ∧ |angularPartial φ p| ≤ J := by
  have hc : Continuous (fun p => |φ p| + |radialPartial φ p| + |angularPartial φ p|) :=
    (hφ.continuous.abs.add (contDiff_cylinder_radialPartial hφ).continuous.abs).add
      (contDiff_cylinder_angularPartial hφ).continuous.abs
  have hQ : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨J, hJ⟩ := hQ.bddAbove_image hc.continuousOn
  refine ⟨max J 0, le_max_right _ _, ?_⟩
  intro p hp
  have hb := (hJ ⟨p, hp, rfl⟩).trans (le_max_left J 0)
  exact ⟨by linarith only [hb, abs_nonneg (radialPartial φ p), abs_nonneg (angularPartial φ p)],
    by linarith only [hb, abs_nonneg (φ p), abs_nonneg (angularPartial φ p)],
    by linarith only [hb, abs_nonneg (φ p), abs_nonneg (radialPartial φ p)]⟩

private theorem cubic_cutoff_commutator_tendsto
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (hφ : ContDiff ℝ ∞ φ)
    (hL : MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ) 2 (canonicalMeasure S K m))
    (hLn : ∀ n, MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)) 2
        (canonicalMeasure S K m)) :
    Tendsto (fun n => (hLn n).toLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)) -
        (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n
          (divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ)))
      atTop (𝓝 0) := by
  obtain ⟨J, hJ, htest⟩ := test_first_jets_bounded hφ
  obtain ⟨Q, hQ, hcut⟩ := n06_intervalTestCutoff_cubic_weighted_bounds
  let L := n06CubicCoefficients (fun p => cylinderWeight p.1) A B C
  let e : ℕ → CanonicalL2 S K m := fun n =>
    (hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) -
      (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ))
  let hOne : MemLp (fun _ : PolarPoint => (1 : ℝ)) 2 (canonicalMeasure S K m) :=
    n06_memLp_canonical_of_continuous m continuous_const
  have hnorm (n : ℕ) : ‖e n‖ ≤
      (10 * (Q / ((n : ℝ) + 1)) * δ * J) * ‖hOne.toLp (fun _ => 1)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub
        ((hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)))
        ((n06InteriorTestCut_memLp hL n).toLp
          (n06InteriorTestCut n (divergenceOperator L φ))),
      MemLp.coeFn_toLp (hLn n), MemLp.coeFn_toLp (n06InteriorTestCut_memLp hL n),
      MemLp.coeFn_toLp hOne,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hsub hnp hcp h1 hp
    change ‖((hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) -
      (n06InteriorTestCut_memLp hL n).toLp
        (n06InteriorTestCut n (divergenceOperator L φ))) p‖ ≤ _
    rw [hsub, Pi.sub_apply, hnp, hcp, h1, norm_one, mul_one, Real.norm_eq_abs]
    have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hpr : p.1 ∈ Icc (0 : ℝ) 1 := by
      simpa only [hl, hr] using Ioo_subset_Icc_self hp.1
    obtain ⟨hφ₀, hφr, hφt⟩ := htest p ⟨hpr, Ioc_subset_Icc_self hp.2⟩
    obtain ⟨hA₀, hB₀, _, hAr, hBt, _, _⟩ := hjet p hpU
    obtain ⟨hχ₁, hχ₂⟩ := hcut n p.1 hpr
    have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
    exact n06_cubic_radialCutoff_error_abs_le
      ((hA.contDiffAt hn).differentiableAt (by simp))
      ((hB.contDiffAt hn).differentiableAt (by simp))
      ((hC.contDiffAt hn).differentiableAt (by simp)) hφ
      (contDiff_intervalTestCutoff 0 1 n) hpr hδ hJ (div_nonneg hQ (by positivity))
      hA₀ hB₀ hAr hBt hφ₀ hφr hφt hχ₁ hχ₂
  have hrate : Tendsto (fun n : ℕ => Q / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Q
  have hbound : Tendsto
      (fun n : ℕ => (10 * (Q / ((n : ℝ) + 1)) * δ * J) * ‖hOne.toLp (fun _ => 1)‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      (((hrate.const_mul 10).mul_const δ).mul_const J).mul_const ‖hOne.toLp (fun _ => 1)‖
  change Tendsto e atTop (𝓝 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun n => norm_nonneg (e n)) hnorm hbound

/-- The true cubic divergence of the compact tests converges in the
original L² space to its value on the closed-cylinder test. The only
coefficient assumptions are open-strip smoothness and bounded first
jets. Both L² membership statements are proved here. -/
theorem n06_cubic_closedTest_cutoff_tendsto
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (hφ : ContDiff ℝ ∞ φ) :
    ∃ hL : MemLp (divergenceOperator
        (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ) 2
        (canonicalMeasure S K m),
      ∃ hLn : ∀ n, MemLp (divergenceOperator
        (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)) 2
          (canonicalMeasure S K m),
        Tendsto (fun n => (hLn n).toLp (divergenceOperator
          (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)))
          atTop (𝓝 (hL.toLp (divergenceOperator
            (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ))) := by
  let L := n06CubicCoefficients (fun p => cylinderWeight p.1) A B C
  let hL : MemLp (divergenceOperator L φ) 2 (canonicalMeasure S K m) :=
    n06_cubic_closedTest_memLp hl hr hδ hA hB hC hjet hφ
  let hLn : ∀ n, MemLp (divergenceOperator L (n06InteriorTestCut n φ)) 2
      (canonicalMeasure S K m) := fun n =>
    n06_cubic_closedTest_memLp hl hr hδ hA hB hC hjet (n06InteriorTestCut_contDiff n hφ)
  refine ⟨hL, hLn, ?_⟩
  have hcut := n06InteriorTestCut_tendsto hl hr hL
  have herr := cubic_cutoff_commutator_tendsto hl hr hδ hA hB hC hjet hφ hL hLn
  have hs := hcut.add herr
  have heq : (fun n =>
      (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ)) +
        ((hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) -
          (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ)))) =
      fun n => (hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) := by
    funext n
    abel
  dsimp only [L] at heq hs
  simpa only [heq, add_zero] using hs

end ContinuousFlexibility.Analysis
