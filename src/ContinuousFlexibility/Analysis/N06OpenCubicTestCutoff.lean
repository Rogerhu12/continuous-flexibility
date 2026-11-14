module

public import ContinuousFlexibility.Analysis.N06CubicCutoffLp
public import ContinuousFlexibility.Analysis.N06NegativeCurrentTestLp
public import ContinuousFlexibility.Analysis.N06PhysicalPairingLimits

/-!
# Cubic test cutoffs with only open-strip smoothness

The actual inverse coordinate is specified on the open canonical strip.
No boundary value or extension of that totalized inverse is needed here.
Three genuine L2 test jets control the cutoff commutator, since the cubic
weights absorb the radial cutoff derivatives. Compact canonical tests
then converge in the actual cubic operator pairing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- The cutoff itself supplies a genuine global smooth test; smoothness
of its input is used only where the cutoff can be nonzero. -/
theorem n06InteriorTestCut_contDiff_of_open
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m)) (n : ℕ) :
    ContDiff ℝ ∞ (n06InteriorTestCut n φ) := by
  have hU : ContDiffOn ℝ ∞ φ (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    simpa only [canonicalOpen, hl, hr] using hφ
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ∈ tsupport (intervalTestCutoff 0 1 n)
  · exact ((contDiff_intervalTestCutoff 0 1 n).comp contDiff_fst).contDiffAt.mul
      (hU.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨intervalTestCutoff_tsupport_subset 0 1 n hp, mem_univ _⟩))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto p).eventually
      ((isClosed_tsupport (intervalTestCutoff 0 1 n)).isOpen_compl.mem_nhds hp)] with q hq
    change intervalTestCutoff 0 1 n q.1 * φ q = 0
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

theorem n06InteriorTestCut_canonicalTest_of_open
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hpφ : ∀ p ∈ canonicalOpen S K m, φ (p + (0, Real.pi)) = φ p) (n : ℕ) :
    CanonicalTest S K m (n06InteriorTestCut n φ) := by
  refine ⟨n06InteriorTestCut_contDiff_of_open hl hr hφ n, ?_,
    tsupport (intervalTestCutoff 0 1 n), intervalTestCutoff_hasCompactSupport 0 1 n, ?_, ?_⟩
  · intro p
    simp only [n06InteriorTestCut, Prod.fst_add, add_zero]
    by_cases hp : p.1 ∈ Ioo (0 : ℝ) 1
    · have hpc : p ∈ canonicalOpen S K m := by
        simpa only [canonicalOpen, hl, hr, Set.mem_prod] using And.intro hp (mem_univ p.2)
      rw [hpφ p hpc]
    · have hz : intervalTestCutoff 0 1 n p.1 = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hp (intervalTestCutoff_tsupport_subset 0 1 n h))
      rw [hz, zero_mul, zero_mul]
  · simpa only [hl, hr] using intervalTestCutoff_tsupport_subset 0 1 n
  · intro r hr θ
    simp only [n06InteriorTestCut, image_eq_zero_of_notMem_tsupport hr, zero_mul]

/-- The established pointwise commutator estimate depends only on the
germ of the test, so open-strip smoothness suffices. -/
theorem n06_cubic_radialCutoff_error_abs_le_of_open
    {A B C φ : PolarPoint → ℝ} {χ : ℝ → ℝ} {p : PolarPoint} {δ J ε : ℝ}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m)) (hpU : p ∈ canonicalOpen S K m)
    (hχ : ContDiff ℝ ∞ χ) (hp : p.1 ∈ Icc (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hε : 0 ≤ ε)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hφ₀ : |φ p| ≤ J) (hφr : |radialPartial φ p| ≤ J) (hφt : |angularPartial φ p| ≤ J)
    (hχ₁ : |cylinderWeight p.1 ^ 2 * deriv χ p.1| ≤ ε)
    (hχ₂ : |cylinderWeight p.1 ^ 3 * deriv (deriv χ) p.1| ≤ ε) :
    |divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p| ≤ 10 * ε * δ * J := by
  obtain ⟨g, hg, he⟩ := n06_exists_smooth_strip_germ hφ hpU
  have hr : radialPartial g p = radialPartial φ p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
  have ht : angularPartial g p = angularPartial φ p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (0, 1)) (he.fderiv_eq (𝕜 := ℝ))
  have hcut : (fun q : PolarPoint => χ q.1 * g q) =ᶠ[𝓝 p]
      (fun q => χ q.1 * φ q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have h := n06_cubic_radialCutoff_error_abs_le hA hB hC hg hχ hp hδ hJ hε
    hA₀ hB₀ hAr hBt (by simpa only [he.eq_of_nhds] using hφ₀)
    (by simpa only [hr] using hφr) (by simpa only [ht] using hφt) hχ₁ hχ₂
  simpa only [n06_divergenceOperator_input_congr_germ _ hcut,
    n06_divergenceOperator_input_congr_germ _ he] using h

/-- The cubic operator cutoffs converge in L2 using the actual first
test jets, without any test extension through the radial endpoints. -/
theorem n06_cubic_openTest_cutoff_tendsto
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hφ₀ : MemLp φ 2 (canonicalMeasure S K m))
    (hφr : MemLp (radialPartial φ) 2 (canonicalMeasure S K m))
    (hφt : MemLp (angularPartial φ) 2 (canonicalMeasure S K m))
    (hL : MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ) 2 (canonicalMeasure S K m)) :
    ∃ hLn : ∀ n, MemLp (divergenceOperator
        (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)) 2
          (canonicalMeasure S K m),
      Tendsto (fun n => (hLn n).toLp (divergenceOperator
        (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) (n06InteriorTestCut n φ)))
        atTop (𝓝 (hL.toLp (divergenceOperator
          (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ))) := by
  let L := n06CubicCoefficients (fun p => cylinderWeight p.1) A B C
  let hLn (n : ℕ) : MemLp (divergenceOperator L (n06InteriorTestCut n φ)) 2
      (canonicalMeasure S K m) :=
    n06_cubic_closedTest_memLp hl hr hδ hA hB hC hjet
      (n06InteriorTestCut_contDiff_of_open hl hr hφ n)
  let J : PolarPoint → ℝ := fun p => |φ p| + |radialPartial φ p| + |angularPartial φ p|
  have hJ : MemLp J 2 (canonicalMeasure S K m) := by
    have hsum := (hφ₀.norm.add hφr.norm).add hφt.norm
    change MemLp (fun p => ‖φ p‖ + ‖radialPartial φ p‖ + ‖angularPartial φ p‖)
      2 (canonicalMeasure S K m) at hsum
    simpa only [J, Real.norm_eq_abs] using hsum
  have hJpos (p : PolarPoint) : 0 ≤ J p :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  obtain ⟨Q, hQ, hcut⟩ := n06_intervalTestCutoff_cubic_weighted_bounds
  let e : ℕ → CanonicalL2 S K m := fun n =>
    (hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) -
      (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ))
  have hnorm (n : ℕ) : ‖e n‖ ≤
      (10 * (Q / ((n : ℝ) + 1)) * δ) * ‖hJ.toLp J‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub
        ((hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)))
        ((n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ))),
      (hLn n).coeFn_toLp, (n06InteriorTestCut_memLp hL n).coeFn_toLp,
      hJ.coeFn_toLp, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
        with p hsub hnp hcp hjp hp
    change ‖((hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) -
      (n06InteriorTestCut_memLp hL n).toLp
        (n06InteriorTestCut n (divergenceOperator L φ))) p‖ ≤ _
    rw [hsub, Pi.sub_apply, hnp, hcp, hjp, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hJpos p)]
    have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hpr : p.1 ∈ Icc (0 : ℝ) 1 := by
      simpa only [hl, hr] using Ioo_subset_Icc_self hp.1
    obtain ⟨hA₀, hB₀, _, hAr, hBt, _, _⟩ := hjet p hpU
    obtain ⟨hχ₁, hχ₂⟩ := hcut n p.1 hpr
    have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
    exact n06_cubic_radialCutoff_error_abs_le_of_open
      ((hA.contDiffAt hn).differentiableAt (by simp))
      ((hB.contDiffAt hn).differentiableAt (by simp))
      ((hC.contDiffAt hn).differentiableAt (by simp)) hφ hpU
      (contDiff_intervalTestCutoff 0 1 n) hpr hδ (hJpos p) (div_nonneg hQ (by positivity))
      hA₀ hB₀ hAr hBt
      (by dsimp only [J]; linarith only [abs_nonneg (radialPartial φ p), abs_nonneg (angularPartial φ p)])
      (by dsimp only [J]; linarith only [abs_nonneg (φ p), abs_nonneg (angularPartial φ p)])
      (by dsimp only [J]; linarith only [abs_nonneg (φ p), abs_nonneg (radialPartial φ p)])
      hχ₁ hχ₂
  have hrate : Tendsto (fun n : ℕ => Q / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Q
  have hbound : Tendsto (fun n : ℕ => (10 * (Q / ((n : ℝ) + 1)) * δ) * ‖hJ.toLp J‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      ((hrate.const_mul 10).mul_const δ).mul_const ‖hJ.toLp J‖
  have herr : Tendsto e atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using squeeze_zero (fun n => norm_nonneg (e n)) hnorm hbound
  refine ⟨hLn, ?_⟩
  have hs := (n06InteriorTestCut_tendsto hl hr hL).add herr
  have heq : (fun n =>
      (n06InteriorTestCut_memLp hL n).toLp (n06InteriorTestCut n (divergenceOperator L φ)) + e n) =
      fun n => (hLn n).toLp (divergenceOperator L (n06InteriorTestCut n φ)) := by
    funext n
    dsimp only [e]
    abel
  dsimp only [L] at heq hs
  simpa only [heq, add_zero] using hs

end ContinuousFlexibility.Analysis
