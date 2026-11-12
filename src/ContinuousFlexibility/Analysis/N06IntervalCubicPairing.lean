import ContinuousFlexibility.Analysis.N06IntervalCubicCommutator
import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# The actual cubic weak pairing at both endpoints

Compact tests are cut off inside the original canonical interval.  The
actual two-endpoint cubic factor makes their commutator converge to zero
in the original L2 space.  This extends the same compact weak equation
to an open-smooth test with genuine L2 first jets and L2 operator image;
no endpoint value of a coefficient or zero trace of the test is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n06CanonicalIntervalTestCut (K : CanonicalData S) (m n : ℕ)
    (φ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => intervalTestCutoff (K.left m) (K.right m) n p.1 * φ p

theorem n06CanonicalIntervalTestCut_memLp
    {φ : PolarPoint → ℝ} (hφ : MemLp φ 2 (canonicalMeasure S K m)) (n : ℕ) :
    MemLp (n06CanonicalIntervalTestCut K m n φ) 2 (canonicalMeasure S K m) := by
  apply hφ.of_le
    (((contDiff_intervalTestCutoff (K.left m) (K.right m) n).continuous.comp
      continuous_fst).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  filter_upwards [] with p
  change ‖intervalTestCutoff (K.left m) (K.right m) n p.1 * φ p‖ ≤ ‖φ p‖
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (intervalTestCutoff_nonneg (K.left m) (K.right m) n p.1)]
  exact (mul_le_mul_of_nonneg_right
    (intervalTestCutoff_le_one (K.left m) (K.right m) n p.1)
    (abs_nonneg (φ p))).trans_eq (one_mul _)

theorem n06CanonicalIntervalTestCut_tendsto
    {φ : PolarPoint → ℝ} (hφ : MemLp φ 2 (canonicalMeasure S K m)) :
    Tendsto (fun n => (n06CanonicalIntervalTestCut_memLp hφ n).toLp
      (n06CanonicalIntervalTestCut K m n φ)) atTop (𝓝 (hφ.toLp φ)) := by
  have hdom : MemLp (fun p => |φ p|) 2 (canonicalMeasure S K m) := by
    simpa only [Real.norm_eq_abs] using hφ.norm
  apply spaces_tendsto_toLp_of_dominated
    (fun n => n06CanonicalIntervalTestCut_memLp hφ n) hφ hdom
  · apply Eventually.of_forall
    intro n
    filter_upwards [] with p
    have hc : |intervalTestCutoff (K.left m) (K.right m) n p.1 - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · linarith only [intervalTestCutoff_nonneg (K.left m) (K.right m) n p.1]
      · linarith only [intervalTestCutoff_le_one (K.left m) (K.right m) n p.1]
    calc
      |n06CanonicalIntervalTestCut K m n φ p - φ p| =
          |intervalTestCutoff (K.left m) (K.right m) n p.1 - 1| * |φ p| := by
        rw [← abs_mul]
        congr 1
        dsimp only [n06CanonicalIntervalTestCut]
        ring
      _ ≤ 1 * |φ p| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = |φ p| := one_mul _
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    simpa only [n06CanonicalIntervalTestCut, one_mul] using
      (tendsto_intervalTestCutoff hp.1).mul_const (φ p)

theorem n06CanonicalIntervalTestCut_contDiff
    {φ : PolarPoint → ℝ} (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m)) (n : ℕ) :
    ContDiff ℝ ∞ (n06CanonicalIntervalTestCut K m n φ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ∈ tsupport (intervalTestCutoff (K.left m) (K.right m) n)
  · exact ((contDiff_intervalTestCutoff (K.left m) (K.right m) n).comp
      contDiff_fst).contDiffAt.mul
      (hφ.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨intervalTestCutoff_tsupport_subset (K.left m) (K.right m) n hp, mem_univ _⟩))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto p).eventually
      ((isClosed_tsupport (intervalTestCutoff (K.left m) (K.right m) n)).isOpen_compl.mem_nhds hp)]
      with q hq
    change intervalTestCutoff (K.left m) (K.right m) n q.1 * φ q = 0
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

theorem n06CanonicalIntervalTestCut_test
    {φ : PolarPoint → ℝ} (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hpφ : ∀ p ∈ canonicalOpen S K m, φ (p + (0, Real.pi)) = φ p) (n : ℕ) :
    CanonicalTest S K m (n06CanonicalIntervalTestCut K m n φ) := by
  refine ⟨n06CanonicalIntervalTestCut_contDiff hφ n, ?_,
    tsupport (intervalTestCutoff (K.left m) (K.right m) n),
    intervalTestCutoff_hasCompactSupport (K.left m) (K.right m) n,
    intervalTestCutoff_tsupport_subset (K.left m) (K.right m) n, ?_⟩
  · intro p
    simp only [n06CanonicalIntervalTestCut, Prod.fst_add, add_zero]
    by_cases hp : p.1 ∈ Ioo (K.left m) (K.right m)
    · rw [hpφ p ⟨hp, mem_univ _⟩]
    · have hz : intervalTestCutoff (K.left m) (K.right m) n p.1 = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hp (intervalTestCutoff_tsupport_subset (K.left m) (K.right m) n h))
      rw [hz, zero_mul, zero_mul]
  · intro r hr θ
    simp only [n06CanonicalIntervalTestCut, image_eq_zero_of_notMem_tsupport hr, zero_mul]

private theorem interval_weight_bounds (a b : ℝ) {x : ℝ} (hx : x ∈ Icc a b) :
    DifferentiableAt ℝ (fun y => (y - a) * (b - y)) x ∧
    |(x - a) * (b - x)| ≤ 1 + (b - a) + (b - a) ^ 2 ∧
    |deriv (fun y => (y - a) * (b - y)) x| ≤ 1 + (b - a) + (b - a) ^ 2 := by
  have hderiv := ((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).const_sub b)
  have he : deriv (fun y => (y - a) * (b - y)) x = (b - x) - (x - a) := by
    simpa only [id_eq, one_mul, mul_neg_one, sub_eq_add_neg] using hderiv.deriv
  have hℓ : 0 ≤ b - a := sub_nonneg.mpr (hx.1.trans hx.2)
  have h0 : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have h1 : 0 ≤ b - x := sub_nonneg.mpr hx.2
  have hbound : (x - a) * (b - x) ≤ (b - a) ^ 2 := by
    simpa only [pow_two] using mul_le_mul
      (show x - a ≤ b - a by linarith only [hx.2])
      (show b - x ≤ b - a by linarith only [hx.1]) h1 hℓ
  refine ⟨hderiv.differentiableAt, ?_, ?_⟩
  · rw [abs_of_nonneg (mul_nonneg h0 h1)]
    linarith only [hbound, hℓ]
  · rw [he]
    have hs : |(b - x) - (x - a)| ≤ b - a :=
      abs_le.mpr ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
    linarith only [hs, sq_nonneg (b - a)]

/-- Strong convergence in the original canonical L2 space. The proof
constructs the L2 operator images of the compact cutoffs from the
commutator; they are not an additional hypothesis. -/
theorem n06_intervalCubic_cutoff_tendsto
    (hlen : K.left m ≤ K.right m)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hφ₀ : MemLp φ 2 (canonicalMeasure S K m))
    (hφr : MemLp (radialPartial φ) 2 (canonicalMeasure S K m))
    (hφt : MemLp (angularPartial φ) 2 (canonicalMeasure S K m))
    (hL : MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C) φ)
        2 (canonicalMeasure S K m)) :
    ∃ hLn : ∀ n, MemLp (divergenceOperator
        (n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C)
          (n06CanonicalIntervalTestCut K m n φ)) 2 (canonicalMeasure S K m),
      Tendsto (fun n => (hLn n).toLp (divergenceOperator
        (n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C)
          (n06CanonicalIntervalTestCut K m n φ)))
        atTop (𝓝 (hL.toLp (divergenceOperator
          (n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C) φ))) := by
  let L := n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C
  let J : PolarPoint → ℝ := fun p => |φ p| + |radialPartial φ p| + |angularPartial φ p|
  have hJ : MemLp J 2 (canonicalMeasure S K m) := by
    have hsum := (hφ₀.norm.add hφr.norm).add hφt.norm
    change MemLp (fun p => ‖φ p‖ + ‖radialPartial φ p‖ + ‖angularPartial φ p‖)
      2 (canonicalMeasure S K m) at hsum
    simpa only [J, Real.norm_eq_abs] using hsum
  have hJpos (p : PolarPoint) : 0 ≤ J p :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  let D : ℝ := 1 + (K.right m - K.left m) + (K.right m - K.left m) ^ 2
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [sub_nonneg.mpr hlen, sq_nonneg (K.right m - K.left m)]
  obtain ⟨Q, hQ, hcut⟩ := n06_intervalCutoff_cubic_weighted_bounds (K.left m) (K.right m) hlen
  let c : ℕ → ℝ := fun n => 10 * D * (Q / ((n : ℝ) + 1)) * δ
  let E : ℕ → PolarPoint → ℝ := fun n p =>
    divergenceOperator L (n06CanonicalIntervalTestCut K m n φ) p -
      n06CanonicalIntervalTestCut K m n (divergenceOperator L φ) p
  have hEbound (n : ℕ) : ∀ᵐ p ∂canonicalMeasure S K m, |E n p| ≤ c n * J p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hpr : p.1 ∈ Icc (K.left m) (K.right m) := Ioo_subset_Icc_self hp.1
    obtain ⟨hd, hd₀, hd₁⟩ := interval_weight_bounds (K.left m) (K.right m) hpr
    obtain ⟨hA₀, hB₀, hAr, hBt⟩ := hjet p hpU
    obtain ⟨hχ₁, hχ₂⟩ := hcut n p.1 hpr
    have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
    exact n06_radialCubic_cutoff_error_bound_on hd
      ((hA.contDiffAt hn).differentiableAt (by simp))
      ((hB.contDiffAt hn).differentiableAt (by simp))
      ((hC.contDiffAt hn).differentiableAt (by simp)) hφ hpU
      (contDiff_intervalTestCutoff (K.left m) (K.right m) n)
      hD hδ (hJpos p) (div_nonneg hQ (by positivity)) hd₀ hd₁
      hA₀ hB₀ hAr hBt
      (by dsimp only [J]; linarith only [abs_nonneg (radialPartial φ p), abs_nonneg (angularPartial φ p)])
      (by dsimp only [J]; linarith only [abs_nonneg (φ p), abs_nonneg (angularPartial φ p)])
      (by dsimp only [J]; linarith only [abs_nonneg (φ p), abs_nonneg (radialPartial φ p)])
      hχ₁ hχ₂
  have hE (n : ℕ) : MemLp (E n) 2 (canonicalMeasure S K m) := by
    apply hJ.of_le_mul ((n06_divergenceOperator_measurable L _).aestronglyMeasurable.sub
      (n06CanonicalIntervalTestCut_memLp hL n).aestronglyMeasurable)
    filter_upwards [hEbound n] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hJpos p)] using hp
  have hLn (n : ℕ) : MemLp (divergenceOperator L (n06CanonicalIntervalTestCut K m n φ))
      2 (canonicalMeasure S K m) := by
    have hsum := (n06CanonicalIntervalTestCut_memLp hL n).add (hE n)
    have he : n06CanonicalIntervalTestCut K m n (divergenceOperator L φ) + E n =
        divergenceOperator L (n06CanonicalIntervalTestCut K m n φ) := by
      funext p
      change _ + (_ - _) = _
      ring
    rw [he] at hsum
    exact hsum
  let e : ℕ → CanonicalL2 S K m := fun n =>
    (hLn n).toLp (divergenceOperator L (n06CanonicalIntervalTestCut K m n φ)) -
      (n06CanonicalIntervalTestCut_memLp hL n).toLp
        (n06CanonicalIntervalTestCut K m n (divergenceOperator L φ))
  have hnorm (n : ℕ) : ‖e n‖ ≤ c n * ‖hJ.toLp J‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub
        ((hLn n).toLp (divergenceOperator L (n06CanonicalIntervalTestCut K m n φ)))
        ((n06CanonicalIntervalTestCut_memLp hL n).toLp
          (n06CanonicalIntervalTestCut K m n (divergenceOperator L φ))),
      (hLn n).coeFn_toLp, (n06CanonicalIntervalTestCut_memLp hL n).coeFn_toLp,
      hJ.coeFn_toLp, hEbound n] with p hsub hnp hcp hjp hp
    change ‖((hLn n).toLp (divergenceOperator L (n06CanonicalIntervalTestCut K m n φ)) -
      (n06CanonicalIntervalTestCut_memLp hL n).toLp
        (n06CanonicalIntervalTestCut K m n (divergenceOperator L φ))) p‖ ≤ _
    rw [hsub, Pi.sub_apply, hnp, hcp, hjp, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hJpos p)]
    exact hp
  have hrate : Tendsto (fun n : ℕ => Q / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Q
  have hbound : Tendsto (fun n : ℕ => c n * ‖hJ.toLp J‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [c, mul_zero, zero_mul] using
      ((hrate.const_mul (10 * D)).mul_const δ).mul_const ‖hJ.toLp J‖
  have herr : Tendsto e atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using squeeze_zero (fun n => norm_nonneg (e n)) hnorm hbound
  refine ⟨hLn, ?_⟩
  have hs := (n06CanonicalIntervalTestCut_tendsto hL).add herr
  have heq : (fun n =>
      (n06CanonicalIntervalTestCut_memLp hL n).toLp
        (n06CanonicalIntervalTestCut K m n (divergenceOperator L φ)) + e n) =
      fun n => (hLn n).toLp (divergenceOperator L (n06CanonicalIntervalTestCut K m n φ)) := by
    funext n
    dsimp only [e]
    abel
  dsimp only [L] at heq hs
  simpa only [heq, add_zero] using hs

/-- The same compact weak source equation is valid for the actual
endpoint-nonzero test. Both integrals retain the original measure. -/
theorem n06_intervalCubic_pairing_of_openTest
    (hlen : K.left m ≤ K.right m)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ)
    (u g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1)) A B C) ψ p
            ∂canonicalMeasure S K m)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hpφ : ∀ p ∈ canonicalOpen S K m, φ (p + (0, Real.pi)) = φ p)
    (hφ₀ : MemLp φ 2 (canonicalMeasure S K m))
    (hφr : MemLp (radialPartial φ) 2 (canonicalMeasure S K m))
    (hφt : MemLp (angularPartial φ) 2 (canonicalMeasure S K m))
    (hL : MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => (p.1 - K.left m) * (K.right m - p.1)) A B C) φ)
        2 (canonicalMeasure S K m)) :
    (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1)) A B C) φ p
          ∂canonicalMeasure S K m := by
  obtain ⟨hLn, hLlim⟩ :=
    n06_intervalCubic_cutoff_tendsto hlen hδ hA hB hC hjet hφ hφ₀ hφr hφt hL
  have hleft := r11b_tendsto_integral_mul_of_L2_tendsto
    (fun n => n06CanonicalIntervalTestCut_memLp hφ₀ n) hφ₀ (Lp.memLp g)
    (n06CanonicalIntervalTestCut_tendsto hφ₀)
  have hright := r11b_tendsto_integral_mul_of_L2_tendsto hLn hL (Lp.memLp u) hLlim
  have hseq : (fun n => ∫ p, n06CanonicalIntervalTestCut K m n φ p * g p
      ∂canonicalMeasure S K m) =
      fun n => ∫ p, divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1)) A B C)
          (n06CanonicalIntervalTestCut K m n φ) p * u p ∂canonicalMeasure S K m := by
    funext n
    simpa only [mul_comm] using hweak _ (n06CanonicalIntervalTestCut_test hφ hpφ n)
  rw [hseq] at hleft
  simpa only [mul_comm] using tendsto_nhds_unique hleft hright

end ContinuousFlexibility.Analysis
