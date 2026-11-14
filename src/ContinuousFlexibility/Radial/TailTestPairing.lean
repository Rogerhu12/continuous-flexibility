module

public import ContinuousFlexibility.Statements.DeepTailOperator
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compact tests for the weighted tail space

The density is assumed smooth and positive only on the open tail. A test has
compact topological support inside that interval. Dividing the test by the
density gives an actual weighted `L²` function, so its ordinary Lebesgue
pairing is a continuous functional on the weighted space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem tail_contDiff_mul_test {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint) :
    ContDiff ℝ ∞ (fun x => T.p x * φ x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact (hp.contDiffAt (isOpen_Ioo.mem_nhds (hs hx))).mul hφ.contDiffAt
  · have he : (fun y => T.p y * φ y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem tail_contDiff_div_test {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint) :
    ContDiff ℝ ∞ (fun x => φ x / T.p x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.div (hp.contDiffAt (isOpen_Ioo.mem_nhds (hs hx)))
      (hpos x (hs hx)).ne'
  · have he : (fun y => φ y / T.p y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem tail_tsupport_div_test {T : DeepTailData} (φ : ℝ → ℝ) :
    tsupport (fun x => φ x / T.p x) ⊆ tsupport φ := by
  apply closure_mono
  intro x hx hzero
  exact hx (by simp only [hzero, zero_div])

theorem tail_density_aemeasurable {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint)) :
    AEMeasurable (fun x => ENNReal.ofReal (T.p x))
      (volume.restrict (Ioo T.entrance T.endpoint)) :=
  (hp.continuousOn.aemeasurable measurableSet_Ioo).ennreal_ofReal

theorem tail_integral_density {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂deepTailMeasure T) =
      ∫ x in Ioo T.entrance T.endpoint, T.p x * f x := by
  rw [deepTailMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (tail_density_aemeasurable hp) (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [ENNReal.toReal_ofReal (hpos x hx).le, smul_eq_mul]

theorem tail_integrable_density_iff {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (f : ℝ → ℝ) :
    Integrable f (deepTailMeasure T) ↔
      IntegrableOn (fun x => T.p x * f x) (Ioo T.entrance T.endpoint) := by
  rw [deepTailMeasure, integrable_withDensity_iff_integrable_smul₀'
    (tail_density_aemeasurable hp) (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [ENNReal.toReal_ofReal (hpos x hx).le, smul_eq_mul]

theorem tail_test_memLp {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint) :
    MemLp φ 2 (deepTailMeasure T) := by
  apply (memLp_two_iff_integrable_sq hφ.continuous.aestronglyMeasurable).mpr
  apply (tail_integrable_density_iff hp hpos _).mpr
  have hcont : Continuous (fun x => T.p x * (φ x) ^ 2) := by
    convert ((tail_contDiff_mul_test hp hφ hs).mul hφ).continuous using 1
    funext x
    ring
  have hc' : HasCompactSupport (fun x => T.p x * (φ x) ^ 2) := by
    apply hc.mono
    intro x hx hzero
    exact hx (by simp only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])
  exact (hcont.integrable_of_hasCompactSupport hc').integrableOn

theorem tail_div_test_memLp {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint) :
    MemLp (fun x => φ x / T.p x) 2 (deepTailMeasure T) :=
  tail_test_memLp hp hpos (tail_contDiff_div_test hp hpos hφ hs)
    (hc.of_isClosed_subset (isClosed_tsupport _) (tail_tsupport_div_test φ))
    ((tail_tsupport_div_test φ).trans hs)

/-- The ordinary test pairing, represented in the weighted Hilbert space. -/
def tailTestPairing (T : DeepTailData) (φ : ℝ → ℝ)
    (hφ : MemLp (fun x => φ x / T.p x) 2 (deepTailMeasure T)) :
    DeepTailL2 T →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp (fun x => φ x / T.p x))

theorem tail_integral_div_test {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hs : Function.support φ ⊆ Ioo T.entrance T.endpoint) (f : ℝ → ℝ) :
    (∫ x, f x * (φ x / T.p x) ∂deepTailMeasure T) = ∫ x, f x * φ x := by
  rw [tail_integral_density hp hpos]
  calc
    (∫ x in Ioo T.entrance T.endpoint, T.p x * (f x * (φ x / T.p x))) =
        ∫ x in Ioo T.entrance T.endpoint, f x * φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      field_simp [(hpos x hx).ne'] <;> ring
    _ = ∫ x, f x * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hzero : φ x = 0 := Function.notMem_support.mp (fun h => hx (hs h))
        simp only [hzero, mul_zero])

theorem tailTestPairing_apply {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint)
    (hφ : MemLp (fun x => φ x / T.p x) 2 (deepTailMeasure T))
    (u : DeepTailL2 T) :
    tailTestPairing T φ hφ u = ∫ x, u x * φ x := by
  rw [tailTestPairing, innerSL_apply_apply, L2.inner_def]
  calc
    (∫ x, ⟪(hφ.toLp (fun x => φ x / T.p x)) x, u x⟫_ℝ ∂deepTailMeasure T) =
        ∫ x, u x * (φ x / T.p x) ∂deepTailMeasure T := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hφ] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial]
    _ = _ := tail_integral_div_test hp hpos ((subset_tsupport φ).trans hs) u

theorem tail_integrable_mul_test {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo T.entrance T.endpoint) (u : DeepTailL2 T) :
    Integrable (fun x => u x * φ x) := by
  have hi := (Lp.memLp u).integrable_mul (tail_div_test_memLp hp hpos hφ hc hs)
  have hw := (tail_integrable_density_iff hp hpos _).mp hi
  have he : IntegrableOn (fun x => u x * φ x) (Ioo T.entrance T.endpoint) := by
    apply hw.congr_fun _ measurableSet_Ioo
    intro x hx
    change T.p x * (u x * (φ x / T.p x)) = u x * φ x
    field_simp [(hpos x hx).ne'] <;> ring
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp he
  intro x hx
  exact hs (subset_tsupport φ (by
    intro hzero
    exact hx (by simp only [hzero, mul_zero])))

/-- Weighted `L²` classes are locally integrable for ordinary Lebesgue measure
inside the tail. No finiteness of the total weighted measure is used. -/
theorem tail_locallyIntegrableOn {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x) (u : DeepTailL2 T) :
    LocallyIntegrableOn (u : ℝ → ℝ) (Ioo T.entrance T.endpoint) := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_Ioo.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := ε / 2, rOut := ε, rIn_pos := half_pos hε,
      rIn_lt_rOut := half_lt_self hε }
  have hχs : tsupport (χ : ℝ → ℝ) ⊆ Ioo T.entrance T.endpoint := by
    rw [χ.tsupport_eq]
    exact hball
  have hi := tail_integrable_mul_test hp hpos χ.contDiff χ.hasCompactSupport hχs u
  refine ⟨Metric.ball x (ε / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (half_pos hε)), ?_⟩
  apply hi.integrableOn.congr_fun _ Metric.isOpen_ball.measurableSet
  intro y hy
  have hχ : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  simp only [hχ, mul_one]

theorem tail_integral_mul_test {T : DeepTailData} {φ : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hs : Function.support φ ⊆ Ioo T.entrance T.endpoint) (f : ℝ → ℝ) :
    (∫ x, f x * φ x ∂deepTailMeasure T) = ∫ x, f x * (T.p x * φ x) := by
  rw [tail_integral_density hp hpos]
  calc
    (∫ x in Ioo T.entrance T.endpoint, T.p x * (f x * φ x)) =
        ∫ x in Ioo T.entrance T.endpoint, f x * (T.p x * φ x) := by
      congr 1
      funext x
      ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hzero : φ x = 0 := Function.notMem_support.mp (fun h => hx (hs h))
      simp only [hzero, mul_zero])

theorem tail_inner_right_of_ae {T : DeepTailData} (u v : DeepTailL2 T) {φ : ℝ → ℝ}
    (hv : (v : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ) :
    ⟪u, v⟫_ℝ = ∫ x, u x * φ x ∂deepTailMeasure T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

theorem tail_unweighted_pairing_congr {T : DeepTailData} {φ u v : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hs : Function.support φ ⊆ Ioo T.entrance T.endpoint)
    (huv : u =ᵐ[deepTailMeasure T] v) :
    (∫ x, u x * φ x) = ∫ x, v x * φ x := by
  rw [← tail_integral_div_test hp hpos hs u, ← tail_integral_div_test hp hpos hs v]
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

end ContinuousFlexibility.Radial
