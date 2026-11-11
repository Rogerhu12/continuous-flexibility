import ContinuousFlexibility.Statements.DeepTailOperator
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Extending a kernel identity to the original test class

Smooth cutoffs with compact topological support inside the interval converge
to one at every interior point. Multiplying an ordinary-support test by these
cutoffs gives convergence in the actual weighted `L²` space. Row integrability
then permits the same limit on the kernel side.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

/-- The cutoff is zero in a collar of width `1 / (n + 1)` at each endpoint
and one outside the larger collars of width `2 / (n + 1)`. -/
def intervalTestCutoff (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * (x - a) - 1) *
    Real.smoothTransition (((n : ℝ) + 1) * (b - x) - 1)

theorem contDiff_intervalTestCutoff (a b : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (intervalTestCutoff a b n) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const))

theorem intervalTestCutoff_nonneg (a b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ intervalTestCutoff a b n x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem intervalTestCutoff_le_one (a b : ℝ) (n : ℕ) (x : ℝ) :
    intervalTestCutoff a b n x ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem intervalTestCutoff_tsupport_subset_closed (a b : ℝ) (n : ℕ) :
    tsupport (intervalTestCutoff a b n) ⊆
      Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hL : 0 < ((n : ℝ) + 1) * (x - a) - 1 := by
    by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
    apply hx
    simp only [intervalTestCutoff, hz, zero_mul]
  have hR : 0 < ((n : ℝ) + 1) * (b - x) - 1 := by
    by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
    apply hx
    simp only [intervalTestCutoff, hz, mul_zero]
  have hLd : 1 / ((n : ℝ) + 1) < x - a := (div_lt_iff₀ hn).mpr (by nlinarith)
  have hRd : 1 / ((n : ℝ) + 1) < b - x := (div_lt_iff₀ hn).mpr (by nlinarith)
  constructor <;> linarith

theorem intervalTestCutoff_hasCompactSupport (a b : ℝ) (n : ℕ) :
    HasCompactSupport (intervalTestCutoff a b n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (intervalTestCutoff_tsupport_subset_closed a b n)

theorem intervalTestCutoff_tsupport_subset (a b : ℝ) (n : ℕ) :
    tsupport (intervalTestCutoff a b n) ⊆ Ioo a b := by
  intro x hx
  have h := intervalTestCutoff_tsupport_subset_closed a b n hx
  have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
  constructor <;> linarith [h.1, h.2]

theorem intervalTestCutoff_eventually_one {a b x : ℝ} (hx : x ∈ Ioo a b) :
    ∀ᶠ n : ℕ in atTop, intervalTestCutoff a b n x = 1 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (2 / (x - a))),
    ht.eventually (eventually_ge_atTop (2 / (b - x)))] with n hL hR
  have hL' := (div_le_iff₀ (sub_pos.mpr hx.1)).mp hL
  have hR' := (div_le_iff₀ (sub_pos.mpr hx.2)).mp hR
  unfold intervalTestCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith only [hL']),
    Real.smoothTransition.one_of_one_le (by linarith only [hR']), mul_one]

theorem tendsto_intervalTestCutoff {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Tendsto (fun n : ℕ => intervalTestCutoff a b n x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [intervalTestCutoff_eventually_one hx] with n hn
  exact hn.symm

/-- The same smooth test, cut off strictly inside the interval. -/
def intervalCutoffTest (a b : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  intervalTestCutoff a b n x * ψ x

theorem contDiff_intervalCutoffTest {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) : ContDiff ℝ ∞ (intervalCutoffTest a b ψ n) :=
  (contDiff_intervalTestCutoff a b n).mul hψ

theorem intervalCutoffTest_hasCompactSupport (a b : ℝ) (ψ : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (intervalCutoffTest a b ψ n) :=
  (intervalTestCutoff_hasCompactSupport a b n).mul_right

theorem intervalCutoffTest_tsupport_subset (a b : ℝ) (ψ : ℝ → ℝ) (n : ℕ) :
    tsupport (intervalCutoffTest a b ψ n) ⊆ Ioo a b :=
  tsupport_mul_subset_left.trans (intervalTestCutoff_tsupport_subset a b n)

theorem abs_intervalCutoffTest_le (a b : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |intervalCutoffTest a b ψ n x| ≤ |ψ x| := by
  rw [intervalCutoffTest, abs_mul, abs_of_nonneg (intervalTestCutoff_nonneg a b n x)]
  exact (mul_le_mul_of_nonneg_right (intervalTestCutoff_le_one a b n x) (abs_nonneg _)).trans_eq
    (one_mul _)

theorem abs_intervalCutoffTest_sub_le (a b : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |intervalCutoffTest a b ψ n x - ψ x| ≤ |ψ x| := by
  have hC : |intervalTestCutoff a b n x - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (intervalTestCutoff_le_one a b n x))]
    linarith only [intervalTestCutoff_nonneg a b n x]
  rw [show intervalCutoffTest a b ψ n x - ψ x =
      (intervalTestCutoff a b n x - 1) * ψ x by unfold intervalCutoffTest; ring, abs_mul]
  exact (mul_le_mul_of_nonneg_right hC (abs_nonneg _)).trans_eq (one_mul _)

theorem tendsto_intervalCutoffTest {a b : ℝ} {ψ : ℝ → ℝ}
    (hs : Function.support ψ ⊆ Ioo a b) (x : ℝ) :
    Tendsto (fun n => intervalCutoffTest a b ψ n x) atTop (𝓝 (ψ x)) := by
  by_cases hx : x ∈ Ioo a b
  · simpa only [intervalCutoffTest, one_mul] using (tendsto_intervalTestCutoff hx).mul_const (ψ x)
  · have hψ : ψ x = 0 := Function.notMem_support.mp (fun h => hx (hs h))
    simpa only [intervalCutoffTest, hψ, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem intervalCutoffTest_memLp {μ : Measure ℝ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hLp : MemLp ψ 2 μ) (n : ℕ) :
    MemLp (intervalCutoffTest a b ψ n) 2 μ := by
  apply hLp.of_le ((contDiff_intervalTestCutoff a b n).continuous.fun_mul hψ).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, intervalCutoffTest] using abs_intervalCutoffTest_le a b ψ n x

private theorem realL2_norm_sq_sub_toLp_measure {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), MemLp.coeFn_toLp hf,
    MemLp.coeFn_toLp hg] with x hsub hfx hgx
  rw [hsub]
  simp only [Pi.sub_apply, hfx, hgx, RCLike.inner_apply, conj_trivial]
  ring

/-- Dominated convergence in the actual real `L²` space for an arbitrary
measure. The measure need not be finite. -/
theorem realL2_tendsto_toLp_of_dominated {μ : Measure ℝ}
    {F : ℕ → ℝ → ℝ} {f B : ℝ → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hf : MemLp f 2 μ) (hB : MemLp B 2 μ)
    (hbound : ∀ n x, |F n x - f x| ≤ |B x|)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  have hsq : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => B x ^ 2)
        (fun n => (((hF n).sub hf).aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)
        hB.integrable_sq
        (fun n => Eventually.of_forall (fun x => by
          change ‖(F n x - f x) ^ 2‖ ≤ B x ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F n x - f x))]
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (F n x - f x)) (hbound n x) 2))
        (Eventually.of_forall (fun x => (hlim x |>.sub_const (f x)).pow 2)))
  have hnormsq : Tendsto (fun n => ‖(hF n).toLp (F n) - hf.toLp f‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [realL2_norm_sq_sub_toLp_measure] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm

/-- Smooth interior cutoffs converge in `L²` to every continuous
ordinary-support test that already represents an `L²` element. -/
theorem tendsto_intervalCutoffTest_toLp {μ : Measure ℝ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hLp : MemLp ψ 2 μ) (hs : Function.support ψ ⊆ Ioo a b) :
    Tendsto (fun n => (intervalCutoffTest_memLp (a := a) (b := b) hψ hLp n).toLp
      (intervalCutoffTest a b ψ n)) atTop (𝓝 (hLp.toLp ψ)) :=
  realL2_tendsto_toLp_of_dominated (intervalCutoffTest_memLp hψ hLp) hLp hLp
    (abs_intervalCutoffTest_sub_le a b ψ) (tendsto_intervalCutoffTest hs)

/-- Row integrability for the target test is enough for the integral limit:
the cutoffs are bounded by one, so `|κ ψ|` is a common dominating function. -/
theorem tendsto_integral_intervalCutoffTest {μ : Measure ℝ} {a b : ℝ}
    {κ ψ : ℝ → ℝ} (hs : Function.support ψ ⊆ Ioo a b)
    (hrow : Integrable (fun y => κ y * ψ y) μ) :
    Tendsto (fun n => ∫ y, κ y * intervalCutoffTest a b ψ n y ∂μ) atTop
      (𝓝 (∫ y, κ y * ψ y ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => ‖κ y * ψ y‖)
  · intro n
    apply ((contDiff_intervalTestCutoff a b n).continuous.aestronglyMeasurable.mul
      hrow.aestronglyMeasurable).congr
    exact Eventually.of_forall fun y => by
      change intervalTestCutoff a b n y * (κ y * ψ y) =
        κ y * intervalCutoffTest a b ψ n y
      unfold intervalCutoffTest
      ring
  · exact hrow.norm
  · intro n
    exact Eventually.of_forall fun y => by
      change |κ y * intervalCutoffTest a b ψ n y| ≤ |κ y * ψ y|
      calc
        _ = |κ y| * |intervalCutoffTest a b ψ n y| := abs_mul _ _
        _ ≤ |κ y| * |ψ y| :=
          mul_le_mul_of_nonneg_left (abs_intervalCutoffTest_le a b ψ n y) (abs_nonneg _)
        _ = _ := (abs_mul _ _).symm
  · exact Eventually.of_forall fun y => (tendsto_intervalCutoffTest hs y).const_mul (κ y)

/-- A continuous `L²` operator represented by one kernel on compact-interior
smooth tests has the same representation on ordinary-support smooth tests.
Only the already-required row integrability for the target test is used. -/
theorem kernel_representation_extend_test {μ : Measure ℝ} {a b : ℝ}
    (G : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (κ : ℝ → ℝ → ℝ)
    (hinterior : ∀ f : Lp ℝ 2 μ, ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (f : ℝ → ℝ) =ᵐ[μ] φ →
      (G f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, κ x y * φ y ∂μ)
    {f : Lp ℝ 2 μ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b)
    (hf : (f : ℝ → ℝ) =ᵐ[μ] ψ)
    (hrow : ∀ᵐ x ∂μ, Integrable (fun y => κ x y * ψ y) μ) :
    (G f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, κ x y * ψ y ∂μ := by
  have hLp : MemLp ψ 2 μ := (memLp_congr_ae hf).mp (Lp.memLp f)
  let φ : ℕ → ℝ → ℝ := intervalCutoffTest a b ψ
  have hφLp (n : ℕ) : MemLp (φ n) 2 μ := intervalCutoffTest_memLp hψ.continuous hLp n
  let fn : ℕ → Lp ℝ 2 μ := fun n => (hφLp n).toLp (φ n)
  have htoLp : hLp.toLp ψ = f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp hLp, hf] with x hx hfx
    exact hx.trans hfx.symm
  have hfn : Tendsto fn atTop (𝓝 f) := by
    have h := tendsto_intervalCutoffTest_toLp (a := a) (b := b) hψ.continuous hLp hs
    rw [htoLp] at h
    exact h
  have hGfn : Tendsto (fun n => G (fn n)) atTop (𝓝 (G f)) :=
    (G.continuous.tendsto f).comp hfn
  obtain ⟨σ, hσ, hσlim⟩ := (tendstoInMeasure_of_tendsto_Lp hGfn).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂μ, ∀ n : ℕ, G (fn n) x = ∫ y, κ x y * φ n y ∂μ := by
    apply ae_all_iff.mpr
    intro n
    exact hinterior (fn n) (φ n) (contDiff_intervalCutoffTest hψ n)
      (intervalCutoffTest_hasCompactSupport a b ψ n)
      (intervalCutoffTest_tsupport_subset a b ψ n) (MemLp.coeFn_toLp (hφLp n))
  filter_upwards [hσlim, hrep, hrow] with x hxLim hxRep hxRow
  have hK : Tendsto (fun n => ∫ y, κ x y * φ n y ∂μ) atTop
      (𝓝 (∫ y, κ x y * ψ y ∂μ)) := tendsto_integral_intervalCutoffTest hs hxRow
  exact tendsto_nhds_unique hxLim
    ((hK.comp hσ.tendsto_atTop).congr' (Eventually.of_forall fun n => (hxRep (σ n)).symm))

/-- The representation clause required by the frozen tail-kernel statement
follows from the compact-topological-support clause without changing the
kernel or the ordinary-support test class. -/
theorem tailKernel_representation_of_interior {T : DeepTailData}
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) (κ : ℝ → ℝ → ℝ)
    (hinterior : ∀ f : DeepTailL2 T, ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ →
      (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y, κ x y * φ y ∂deepTailMeasure T)
    (hrow : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ Ioo T.entrance T.endpoint →
      ∀ᵐ x ∂deepTailMeasure T, Integrable (fun y => κ x y * ψ y) (deepTailMeasure T)) :
    ∀ f : DeepTailL2 T, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ →
      (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y, κ x y * ψ y ∂deepTailMeasure T := by
  intro f ψ hψ hc hs hf
  exact kernel_representation_extend_test G κ hinterior hψ hs hf (hrow ψ hψ hc hs)

end ContinuousFlexibility.Radial
