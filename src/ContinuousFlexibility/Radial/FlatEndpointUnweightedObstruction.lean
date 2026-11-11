import ContinuousFlexibility.Radial.Gauge
import ContinuousFlexibility.Radial.OscillatorCompactCore
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The obstruction to an unweighted inverse at a flat endpoint

The last sentence of manuscript Lemma 6.5 cannot include a global bounded
inverse on `L²(dr)`.  A compact smooth bump approaching a finite positive
flat endpoint has a differential image arbitrarily small relative to its
unweighted norm.  The weighted inverse and the cell-localized estimates
are unaffected by this obstruction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-- A bounded left inverse forces a uniform lower bound on every pair in
its graph.  This elementary implication will be applied to actual compact
smooth radial tests below. -/
theorem no_bounded_left_inverse_of_test_ratios
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (graph : E → F → Prop)
    (htests : ∀ C : ℝ, 0 ≤ C →
      ∃ u v, graph u v ∧ C * ‖v‖ ^ 2 < ‖u‖ ^ 2) :
    ¬ ∃ G : F →L[ℝ] E, ∀ u v, graph u v → G v = u := by
  rintro ⟨G, hG⟩
  obtain ⟨u, v, huv, hsmall⟩ := htests (‖G‖ ^ 2) (sq_nonneg _)
  have hbound : ‖u‖ ≤ ‖G‖ * ‖v‖ := by
    simpa only [hG u v huv] using G.le_opNorm v
  have hsq := mul_self_le_mul_self (norm_nonneg u) hbound
  nlinarith

/-- A fixed smooth cutoff, translated and rescaled into
`[b - 5h, b - h]`, strictly before the endpoint when `h > 0`. -/
def flatEndpointTest (b h x : ℝ) : ℝ :=
  oscillatorCutoff ((x - (b - 3 * h)) / h)

theorem contDiff_flatEndpointTest (b h : ℝ) :
    ContDiff ℝ ∞ (flatEndpointTest b h) :=
  contDiff_oscillatorCutoff.comp
    ((contDiff_id.sub contDiff_const).div_const h)

theorem flatEndpointTest_eq_one {b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Icc (b - 4 * h) (b - 2 * h)) : flatEndpointTest b h x = 1 := by
  apply oscillatorCutoff_eq_one
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh, one_mul]
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem flatEndpointTest_eq_zero {b h x : ℝ} (hh : 0 < h)
    (hx : x ∉ Icc (b - 5 * h) (b - h)) : flatEndpointTest b h x = 0 := by
  apply oscillatorCutoff_eq_zero
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
  by_contra! h
  obtain ⟨hl, hr⟩ := abs_lt.mp h
  exact hx ⟨by linarith, by linarith⟩

theorem flatEndpointTest_tsupport {b h : ℝ} (hh : 0 < h) :
    tsupport (flatEndpointTest b h) ⊆ Icc (b - 5 * h) (b - h) := by
  change closure (Function.support (flatEndpointTest b h)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (flatEndpointTest_eq_zero hh h)

theorem hasCompactSupport_flatEndpointTest {b h : ℝ} (hh : 0 < h) :
    HasCompactSupport (flatEndpointTest b h) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => flatEndpointTest_eq_zero hh hx)

theorem flatEndpointTest_abs_le_one (b h x : ℝ) : |flatEndpointTest b h x| ≤ 1 := by
  rw [abs_of_nonneg (oscillatorCutoff_nonneg _)]
  exact oscillatorCutoff_le_one _

theorem deriv_flatEndpointTest (b h x : ℝ) :
    deriv (flatEndpointTest b h) x =
      deriv oscillatorCutoff ((x - (b - 3 * h)) / h) / h := by
  have hd := (((contDiff_oscillatorCutoff.differentiable (by simp) _).hasDerivAt).comp x
    (((hasDerivAt_id x).sub_const (b - 3 * h)).div_const h)).deriv
  simpa only [flatEndpointTest, Function.comp_def, id_eq, div_eq_mul_inv, one_mul]
    using hd

theorem deriv_deriv_flatEndpointTest (b h x : ℝ) :
    deriv (deriv (flatEndpointTest b h)) x =
      deriv (deriv oscillatorCutoff) ((x - (b - 3 * h)) / h) / h ^ 2 := by
  have h1 := (contDiff_infty_iff_deriv.mp contDiff_oscillatorCutoff).2
  rw [funext (deriv_flatEndpointTest b h)]
  have hd := ((((h1.differentiable (by simp) _).hasDerivAt).comp x
    (((hasDerivAt_id x).sub_const (b - 3 * h)).div_const h)).div_const h).deriv
  simp only [Function.comp_def, id_eq] at hd
  convert hd using 1
  field_simp

theorem flatEndpointTest_derivative_bounds {C b h : ℝ} (hh : 0 < h)
    (hC₁ : ∀ x, |deriv oscillatorCutoff x| ≤ C)
    (hC₂ : ∀ x, |deriv (deriv oscillatorCutoff) x| ≤ C) (x : ℝ) :
    |deriv (flatEndpointTest b h) x| ≤ C / h ∧
      |deriv (deriv (flatEndpointTest b h)) x| ≤ C / h ^ 2 := by
  rw [deriv_flatEndpointTest, deriv_deriv_flatEndpointTest,
    abs_div, abs_div, abs_of_pos hh, abs_of_pos (sq_pos_of_pos hh)]
  exact ⟨div_le_div_of_nonneg_right (hC₁ _) hh.le,
    div_le_div_of_nonneg_right (hC₂ _) (sq_nonneg _)⟩

theorem flatEndpointTest_deriv_eq_zero {b h x : ℝ} (hh : 0 < h)
    (hx : x ∉ Icc (b - 5 * h) (b - h)) :
    deriv (flatEndpointTest b h) x = 0 ∧
      deriv (deriv (flatEndpointTest b h)) x = 0 :=
  ⟨deriv_of_notMem_tsupport (fun h => hx (flatEndpointTest_tsupport hh h)),
    deriv_of_notMem_tsupport (fun h =>
      hx (flatEndpointTest_tsupport hh (tsupport_deriv_subset h)))⟩

/-- Vanishing on an endpoint half-line also makes the actual derivative
vanish there, including at the endpoint itself. -/
theorem deriv_eq_zero_on_endpoint_halfline {w : ℝ → ℝ} {b : ℝ}
    (hw : ∀ x, b ≤ x → w x = 0) : ∀ x, b ≤ x → deriv w x = 0 := by
  intro x hx
  have hd : HasDerivWithinAt w 0 (Ici x) x :=
    (hasDerivWithinAt_const x (Ici x) (0 : ℝ)).congr
      (fun y hy => hw y (hx.trans hy)) (hw x hx)
  exact hd.deriv_eq_zero (uniqueDiffWithinAt_Ici x)

/-- Three integrations of a local third-derivative bound give the
coefficient powers needed for the endpoint tests.  The assumptions here
are the actual smooth zero extension, rather than quasimode estimates. -/
theorem flatEndpoint_coefficient_bounds {w : ℝ → ℝ} {b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hzero : ∀ x, b ≤ x → w x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ, 0 < h → 5 * h ≤ 1 →
      ∀ x ∈ Icc (b - 5 * h) b,
        |w x| ≤ 125 * M * h ^ 3 ∧ |deriv w x| ≤ 25 * M * h ^ 2 := by
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hw2 := (contDiff_infty_iff_deriv.mp hw1).2
  have hw3 := (contDiff_infty_iff_deriv.mp hw2).2
  have hz1 := deriv_eq_zero_on_endpoint_halfline hzero
  have hz2 := deriv_eq_zero_on_endpoint_halfline hz1
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (b - 1) b)).exists_bound_of_continuousOn
    hw3.continuous.continuousOn
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro h hh hh1
  let K : Set ℝ := Icc (b - 5 * h) b
  have hb : b ∈ K := ⟨by linarith, le_rfl⟩
  have hrad (x : ℝ) (hx : x ∈ K) : ‖x - b‖ ≤ 5 * h := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    linarith [hx.1]
  have htop (x : ℝ) (hx : x ∈ K) :
      ‖deriv (deriv (deriv w)) x‖ ≤ M := by
    exact (hC x ⟨by linarith [hx.1], hx.2⟩).trans (le_max_left _ _)
  have hsecond (x : ℝ) (hx : x ∈ K) : ‖deriv (deriv w) x‖ ≤ M * (5 * h) := by
    have hm := (convex_Icc (b - 5 * h) b).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => hw2.differentiable (by simp) y) htop hb hx
    rw [hz2 b le_rfl, sub_zero] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (hrad x hx) hM)
  have hfirst (x : ℝ) (hx : x ∈ K) : ‖deriv w x‖ ≤ M * (5 * h) ^ 2 := by
    have hm := (convex_Icc (b - 5 * h) b).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => hw1.differentiable (by simp) y) hsecond hb hx
    rw [hz1 b le_rfl, sub_zero] at hm
    calc
      ‖deriv w x‖ ≤ (M * (5 * h)) * ‖x - b‖ := hm
      _ ≤ (M * (5 * h)) * (5 * h) :=
        mul_le_mul_of_nonneg_left (hrad x hx) (by positivity)
      _ = M * (5 * h) ^ 2 := by ring
  have hvalue (x : ℝ) (hx : x ∈ K) : ‖w x‖ ≤ M * (5 * h) ^ 3 := by
    have hm := (convex_Icc (b - 5 * h) b).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => hw.differentiable (by simp) y) hfirst hb hx
    rw [hzero b le_rfl, sub_zero] at hm
    calc
      ‖w x‖ ≤ (M * (5 * h) ^ 2) * ‖x - b‖ := hm
      _ ≤ (M * (5 * h) ^ 2) * (5 * h) :=
        mul_le_mul_of_nonneg_left (hrad x hx) (by positivity)
      _ = M * (5 * h) ^ 3 := by ring
  intro x hx
  constructor
  · have hv := hvalue x hx
    rw [Real.norm_eq_abs] at hv
    convert hv using 1 <;> ring
  · have hd := hfirst x hx
    rw [Real.norm_eq_abs] at hd
    convert hd using 1 <;> ring

/-- Product differentiation of the actual radial expression. -/
theorem radialJacobi_expanded_of_contDiff {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (α x : ℝ) :
    radialJacobi α w u x =
      w x * deriv (deriv u) x + deriv w x * deriv u x - α * deriv w x / x * u x := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  rw [radialJacobi, (((hw.differentiable (by simp) x).hasDerivAt).mul
    ((hu1.differentiable (by simp) x).hasDerivAt)).deriv]
  ring

theorem radialJacobi_flatEndpointTest_eq_zero {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) {b h x : ℝ} (hh : 0 < h)
    (hx : x ∉ Icc (b - 5 * h) (b - h)) (α : ℝ) :
    radialJacobi α w (flatEndpointTest b h) x = 0 := by
  obtain ⟨h1, h2⟩ := flatEndpointTest_deriv_eq_zero hh hx
  rw [radialJacobi_expanded_of_contDiff hw (contDiff_flatEndpointTest b h),
    h1, h2, flatEndpointTest_eq_zero hh hx]
  ring

/-- Compact smooth tests away from zero have a genuine unweighted `L²`
radial differential image, despite the displayed coefficient `1 / r`. -/
theorem radialJacobi_compactTest_memLp {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hz : (0 : ℝ) ∉ tsupport u) (α : ℝ) : MemLp (radialJacobi α w u) 2 volume := by
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hflux := (contDiff_infty_iff_deriv.mp (hw.mul hu1)).2
  have hpotential : Continuous (fun x : ℝ => α * deriv w x / x * u x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      have he := notMem_tsupport_iff_eventuallyEq.mp hz
      apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp only [hy, Pi.zero_apply, mul_zero]
    · exact (((continuous_const.mul hw1.continuous).continuousAt.div
        continuous_id.continuousAt hx).mul hu.continuous.continuousAt)
  have hcflux : HasCompactSupport (fun x : ℝ => w x * deriv u x) := hc.deriv.mul_left
  have hcpotential : HasCompactSupport (fun x : ℝ => α * deriv w x / x * u x) := hc.mul_left
  exact (hflux.continuous.sub hpotential).memLp_of_hasCompactSupport
    (hcflux.deriv.sub hcpotential)

/-- The actual differential image has size `O(h)` on the support of the
test.  The coefficient estimates used here are supplied by
`flatEndpoint_coefficient_bounds`. -/
theorem radialJacobi_flatEndpointTest_abs_le {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) {a b h M C : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hh1 : h ≤ 1) (hab : a ≤ b - 5 * h) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hC₁ : ∀ x, |deriv oscillatorCutoff x| ≤ C)
    (hC₂ : ∀ x, |deriv (deriv oscillatorCutoff) x| ≤ C)
    (hcoeff : ∀ x ∈ Icc (b - 5 * h) b,
      |w x| ≤ 125 * M * h ^ 3 ∧ |deriv w x| ≤ 25 * M * h ^ 2)
    (α : ℝ) {x : ℝ} (hx : x ∈ Icc (b - 5 * h) (b - h)) :
    |radialJacobi α w (flatEndpointTest b h) x| ≤
      (150 * M * C + 25 * |α| * M / a) * h := by
  have hax : a ≤ x := hab.trans hx.1
  have hxpos : 0 < x := ha.trans_le hax
  have hxcore : x ∈ Icc (b - 5 * h) b := ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨hwx, hwdx⟩ := hcoeff x hxcore
  obtain ⟨hu1, hu2⟩ := flatEndpointTest_derivative_bounds hh hC₁ hC₂ x
  have hsecond : |w x * deriv (deriv (flatEndpointTest b h)) x| ≤ 125 * M * C * h := by
    rw [abs_mul]
    calc
      _ ≤ (125 * M * h ^ 3) * (C / h ^ 2) :=
        mul_le_mul hwx hu2 (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [ne_of_gt hh]; ring
  have hfirst : |deriv w x * deriv (flatEndpointTest b h) x| ≤ 25 * M * C * h := by
    rw [abs_mul]
    calc
      _ ≤ (25 * M * h ^ 2) * (C / h) :=
        mul_le_mul hwdx hu1 (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [ne_of_gt hh]; ring
  have hpotential : |α * deriv w x / x * flatEndpointTest b h x| ≤
      (25 * |α| * M / a) * h := by
    calc
      _ ≤ |α * deriv w x / x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (flatEndpointTest_abs_le_one b h x)
      _ = |α| * |deriv w x| / x := by rw [abs_div, abs_mul, abs_of_pos hxpos]
      _ ≤ |α| * (25 * M * h ^ 2) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwdx (abs_nonneg _)) hxpos.le
      _ ≤ |α| * (25 * M * h ^ 2) / a :=
        div_le_div_of_nonneg_left (by positivity) ha hax
      _ = (25 * |α| * M / a) * h ^ 2 := by ring
      _ ≤ (25 * |α| * M / a) * h :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  rw [radialJacobi_expanded_of_contDiff hw (contDiff_flatEndpointTest b h)]
  calc
    _ ≤ (|w x * deriv (deriv (flatEndpointTest b h)) x| +
        |deriv w x * deriv (flatEndpointTest b h) x|) +
        |α * deriv w x / x * flatEndpointTest b h x| :=
      (abs_sub_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (125 * M * C * h + 25 * M * C * h) + (25 * |α| * M / a) * h :=
      add_le_add (add_le_add hsecond hfirst) hpotential
    _ = _ := by ring

/-- A plateau of length `2h` provides the lower bound on the unnormalized
test's squared unweighted norm. -/
theorem flatEndpointTest_integral_lower {b h : ℝ} (hh : 0 < h) :
    2 * h ≤ ∫ x : ℝ, flatEndpointTest b h x ^ 2 := by
  let I : Set ℝ := Icc (b - 4 * h) (b - 2 * h)
  have hI : MeasurableSet I := measurableSet_Icc
  have hone : Integrable (I.indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrableOn_const (μ := volume) (C := (1 : ℝ)) (s := I)
      isCompact_Icc.measure_ne_top).integrable_indicator hI
  have hχ := (contDiff_flatEndpointTest b h).continuous.memLp_of_hasCompactSupport
    (μ := volume) (p := 2) (hasCompactSupport_flatEndpointTest hh)
  have hχ₂ : Integrable (fun x : ℝ => flatEndpointTest b h x ^ 2) volume := by
    simpa only [Pi.mul_apply, pow_two] using hχ.integrable_mul hχ
  have hint := integral_mono hone hχ₂ (fun x => by
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx, flatEndpointTest_eq_one hh hx, one_pow]
    · rw [indicator_of_notMem hx]
      exact sq_nonneg _)
  have hlen : b - 4 * h ≤ b - 2 * h := by linarith
  rw [integral_indicator_const _ hI] at hint
  change (volume : Measure ℝ).real (Icc (b - 4 * h) (b - 2 * h)) • (1 : ℝ) ≤ _ at hint
  rw [Real.volume_real_Icc_of_le hlen, smul_eq_mul, mul_one] at hint
  linarith

/-- Integrating a pointwise bound over the support interval gives the
upper bound for the actual radial image. -/
theorem radialJacobi_flatEndpointTest_integral_upper {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) {b h D : ℝ} (hh : 0 < h) (hD : 0 ≤ D)
    (hz : (0 : ℝ) ∉ tsupport (flatEndpointTest b h)) (α : ℝ)
    (hbound : ∀ x ∈ Icc (b - 5 * h) (b - h),
      |radialJacobi α w (flatEndpointTest b h) x| ≤ D * h) :
    (∫ x : ℝ, radialJacobi α w (flatEndpointTest b h) x ^ 2) ≤ 4 * h * (D * h) ^ 2 := by
  let I : Set ℝ := Icc (b - 5 * h) (b - h)
  have hI : MeasurableSet I := measurableSet_Icc
  have himage := radialJacobi_compactTest_memLp hw (contDiff_flatEndpointTest b h)
    (hasCompactSupport_flatEndpointTest hh) hz α
  have hi : Integrable (fun x : ℝ => radialJacobi α w (flatEndpointTest b h) x ^ 2) volume := by
    simpa only [Pi.mul_apply, pow_two] using himage.integrable_mul himage
  have hmajorant : Integrable (I.indicator (fun _ : ℝ => (D * h) ^ 2)) volume :=
    (integrableOn_const (μ := volume) (C := (D * h) ^ 2) (s := I)
      isCompact_Icc.measure_ne_top).integrable_indicator hI
  calc
    _ ≤ ∫ x : ℝ, I.indicator (fun _ : ℝ => (D * h) ^ 2) x := by
      apply integral_mono hi hmajorant
      intro x
      by_cases hx : x ∈ I
      · rw [indicator_of_mem hx, ← sq_abs (radialJacobi α w (flatEndpointTest b h) x)]
        exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD hh.le)).2 (hbound x hx)
      · rw [indicator_of_notMem hx, radialJacobi_flatEndpointTest_eq_zero hw hh hx α]
        norm_num
    _ = _ := by
      have hlen : b - 5 * h ≤ b - h := by linarith
      rw [integral_indicator_const _ hI]
      change (volume : Measure ℝ).real (Icc (b - 5 * h) (b - h)) • (D * h) ^ 2 = _
      rw [Real.volume_real_Icc_of_le hlen, smul_eq_mul]
      ring

end ContinuousFlexibility.Radial
