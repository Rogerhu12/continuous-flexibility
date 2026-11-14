module

public import ContinuousFlexibility.Radial.R11bPhysicalPairing
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth radial cutoffs exhausting the physical annulus

The cutoffs have compact radial support in the open core, stay between
zero and one, and are eventually one at every interior point.  Dominated
convergence therefore extends integrable physical pairings from compact
radial tests without estimating derivatives of the cutoffs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

def referenceRadialCutoff (D : ReferenceData) (n : ℕ) (r : ℝ) : ℝ :=
  smoothTransition (((n : ℝ) + 1) * (r - D.a) - 1) *
    smoothTransition (((n : ℝ) + 1) * (D.b - r) - 1)

theorem referenceRadialCutoff_contDiff (D : ReferenceData) (n : ℕ) :
    ContDiff ℝ ∞ (referenceRadialCutoff D n) := by
  have hl : ContDiff ℝ ∞ (fun r : ℝ => ((n : ℝ) + 1) * (r - D.a) - 1) :=
    (contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hr : ContDiff ℝ ∞ (fun r : ℝ => ((n : ℝ) + 1) * (D.b - r) - 1) :=
    (contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const
  exact (smoothTransition.contDiff.comp hl).mul (smoothTransition.contDiff.comp hr)

theorem referenceRadialCutoff_bounds (D : ReferenceData) (n : ℕ) (r : ℝ) :
    0 ≤ referenceRadialCutoff D n r ∧ referenceRadialCutoff D n r ≤ 1 := by
  refine ⟨mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _), ?_⟩
  unfold referenceRadialCutoff
  calc
    _ ≤ 1 * smoothTransition (((n : ℝ) + 1) * (D.b - r) - 1) :=
      mul_le_mul_of_nonneg_right (smoothTransition.le_one _) (smoothTransition.nonneg _)
    _ ≤ 1 := by
      simpa only [one_mul] using
        (smoothTransition.le_one (((n : ℝ) + 1) * (D.b - r) - 1))

private theorem reference_transition_scaled_zero {c x : ℝ}
    (hc : 0 < c) (hx : x ≤ c⁻¹) : smoothTransition (c * x - 1) = 0 := by
  apply smoothTransition.zero_of_nonpos
  have hm : c * x ≤ 1 := by
    calc
      _ ≤ c * c⁻¹ := mul_le_mul_of_nonneg_left hx hc.le
      _ = 1 := mul_inv_cancel₀ hc.ne'
  linarith

theorem referenceRadialCutoff_compact_support (D : ReferenceData) (n : ℕ) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, referenceRadialCutoff D n r = 0 := by
  let c : ℝ := (n : ℝ) + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨Icc (D.a + c⁻¹) (D.b - c⁻¹), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    change D.a < r ∧ r < D.b
    constructor <;> linarith [hr.1, hr.2]
  · intro r hr
    change smoothTransition (c * (r - D.a) - 1) *
      smoothTransition (c * (D.b - r) - 1) = 0
    by_cases hl : r ≤ D.a + c⁻¹
    · rw [reference_transition_scaled_zero hc (show r - D.a ≤ c⁻¹ by linarith), zero_mul]
    · have hh : D.b - c⁻¹ < r :=
        lt_of_not_ge (fun h => hr ⟨(lt_of_not_ge hl).le, h⟩)
      rw [reference_transition_scaled_zero hc (show D.b - r ≤ c⁻¹ by linarith), mul_zero]

private theorem reference_transition_eventually_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, smoothTransition (((n : ℝ) + 1) * x - 1) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply smoothTransition.one_of_one_le
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right hn' hx.le
  have hNx : 2 < (N : ℝ) * x := (div_lt_iff₀ hx).mp hN
  nlinarith

theorem referenceRadialCutoff_eventually_one {D : ReferenceData} {r : ℝ}
    (hr : r ∈ radialCore D) :
    ∀ᶠ n : ℕ in atTop, referenceRadialCutoff D n r = 1 := by
  filter_upwards [reference_transition_eventually_one (sub_pos.mpr hr.1),
    reference_transition_eventually_one (sub_pos.mpr hr.2)] with n hn₁ hn₂
  simp only [referenceRadialCutoff, hn₁, hn₂, one_mul]

theorem referenceRadialCutoff_test {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hup : Function.Periodic u (0, 2 * Real.pi)) (n : ℕ) :
    RadialTest D (fun x => referenceRadialCutoff D n x.1 * u x) := by
  refine ⟨((referenceRadialCutoff_contDiff D n).comp contDiff_fst).mul hu, ?_, ?_⟩
  · intro x
    simp only [Prod.fst_add, add_zero, hup x]
  · obtain ⟨K, hK, hKcore, hzero⟩ := referenceRadialCutoff_compact_support D n
    refine ⟨K, hK, hKcore, ?_⟩
    intro r hr θ
    change referenceRadialCutoff D n r * u (r, θ) = 0
    rw [hzero r hr, zero_mul]

theorem referenceRadialCutoff_norm_mul_le (D : ReferenceData) (n : ℕ) (r z : ℝ) :
    ‖referenceRadialCutoff D n r * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Real.norm_of_nonneg (referenceRadialCutoff_bounds D n r).1]
  calc
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right
      (referenceRadialCutoff_bounds D n r).2 (norm_nonneg z)
    _ = ‖z‖ := one_mul _

theorem referenceRadialCutoff_mul_integrable {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D)) (n : ℕ) :
    Integrable (fun x => referenceRadialCutoff D n x.1 * f x)
      (radialPhysicalMeasure D) := by
  apply hf.norm.mono'
    (((referenceRadialCutoff_contDiff D n).continuous.comp continuous_fst).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  exact ae_of_all _ (fun x => referenceRadialCutoff_norm_mul_le D n x.1 (f x))

theorem reference_integral_cutoff_tendsto {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D)) :
    Tendsto (fun n => ∫ x, referenceRadialCutoff D n x.1 * f x
      ∂radialPhysicalMeasure D) atTop (𝓝 (∫ x, f x ∂radialPhysicalMeasure D)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact ((referenceRadialCutoff_contDiff D n).continuous.comp
      continuous_fst).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact ae_of_all _ (fun x => referenceRadialCutoff_norm_mul_le D n x.1 (f x))
  · have hmem : ∀ᵐ x ∂radialPhysicalMeasure D,
        x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hmem] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [referenceRadialCutoff_eventually_one hx.1] with n hn
    simp only [hn, one_mul]

theorem reference_mean_cutoff_tendsto {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : Integrable f (radialPhysicalMeasure D)) :
    Tendsto (fun n => ∫ r in D.a..D.b, radialAngularMean
      (fun θ => referenceRadialCutoff D n r * f (r, θ))) atTop
        (𝓝 (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ)))) := by
  have ht := (reference_integral_cutoff_tendsto hf).const_mul ((2 * Real.pi)⁻¹)
  have heq (n : ℕ) :
      (∫ r in D.a..D.b, radialAngularMean
        (fun θ => referenceRadialCutoff D n r * f (r, θ))) =
      (2 * Real.pi)⁻¹ * ∫ x, referenceRadialCutoff D n x.1 * f x ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hab (referenceRadialCutoff_mul_integrable hf n)
  have hlim := r11b_integral_angularMean_eq hab hf
  simpa only [heq, hlim] using ht

end ContinuousFlexibility.Radial
