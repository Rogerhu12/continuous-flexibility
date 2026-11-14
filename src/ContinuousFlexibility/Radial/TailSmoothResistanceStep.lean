module

public import ContinuousFlexibility.Radial.TailResistanceTransport
public import ContinuousFlexibility.Radial.MorsePositiveJoin
public import Mathlib.Topology.Order.ProjIcc

/-!
# Smooth steps with inverse-resistance energy

A fixed smooth transition is applied to the resistance coordinate, leaving
constant collars at both ends. The density needs to be smooth only inside
the edge. A continuous positive clamped extension supplies a global
resistance coordinate; the transition is locally constant wherever that
extension may fail to be smooth.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

theorem tail_transition_derivative_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv smoothTransition x| ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_morseJoinWeight_jet_bound 1
  have he : morseJoinRightWeight 2 2 = smoothTransition := by
    funext x
    unfold morseJoinRightWeight
    congr 1
    ring
  refine ⟨M, hM, fun x => ?_⟩
  have hh := (hb 0 2 2 (by norm_num) x).2
  rw [he, iteratedDeriv_one] at hh
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), pow_one, mul_one] using hh

def tailSmoothResistanceStep (p : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  smoothTransition ((2 / tailResistanceChart p a b) * tailResistanceChart p a x - 1 / 2)

theorem tailResistanceChart_contDiffOn {p : ℝ → ℝ} {a b : ℝ}
    (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (hps : ContDiffOn ℝ ∞ p (Ioo a b)) :
    ContDiffOn ℝ ∞ (tailResistanceChart p a) (Ioo a b) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mpr
  refine ⟨fun x _ => (hasDerivAt_tailResistanceChart hp hpos a x).differentiableAt.differentiableWithinAt,
    ?_⟩
  have he : deriv (tailResistanceChart p a) = fun x => (p x)⁻¹ :=
    funext fun x => (hasDerivAt_tailResistanceChart hp hpos a x).deriv
  rw [he]
  exact hps.inv (fun x _ => (hpos x).ne')

theorem tailSmoothResistanceStep_spec {p : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (hps : ContDiffOn ℝ ∞ p (Ioo a b)) (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |deriv smoothTransition x| ≤ M) :
    ContDiff ℝ ∞ (tailSmoothResistanceStep p a b) ∧
    (∀ x, 0 ≤ tailSmoothResistanceStep p a b x ∧ tailSmoothResistanceStep p a b x ≤ 1) ∧
    (∀ x, x ≤ a → tailSmoothResistanceStep p a b x = 0) ∧
    (∀ x, b ≤ x → tailSmoothResistanceStep p a b x = 1) ∧
    (tailSmoothResistanceStep p a b =ᶠ[𝓝 a] fun _ => 0) ∧
    (tailSmoothResistanceStep p a b =ᶠ[𝓝 b] fun _ => 1) ∧
    tsupport (deriv (tailSmoothResistanceStep p a b)) ⊆ Ioo a b ∧
    (∫ x in a..b, p x * deriv (tailSmoothResistanceStep p a b) x ^ 2) ≤
      4 * (M + 1) ^ 2 / (∫ x in a..b, (p x)⁻¹) := by
  let s : ℝ → ℝ := tailResistanceChart p a
  let R : ℝ := s b
  let A : ℝ → ℝ := fun x => (2 / R) * s x - 1 / 2
  let θ : ℝ → ℝ := tailSmoothResistanceStep p a b
  have hs : StrictMono s := tailResistanceChart_strictMono hp hpos a
  have hsa : s a = 0 := by simp only [s, tailResistanceChart, intervalIntegral.integral_same]
  have hR : 0 < R := by
    have h := hs hab
    rwa [hsa] at h
  have hsC : Continuous s := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_tailResistanceChart hp hpos a x).continuousAt)
  have hAC : Continuous A := (continuous_const.mul hsC).sub continuous_const
  have hAmono : StrictMono A := by
    intro x y hxy
    exact sub_lt_sub_right (mul_lt_mul_of_pos_left (hs hxy) (div_pos (by norm_num) hR)) _
  have hAa : A a = -(1 / 2 : ℝ) := by simp only [A, hsa, mul_zero, zero_sub]
  have hAb : A b = (3 / 2 : ℝ) := by
    change (2 / R) * R - 1 / 2 = 3 / 2
    field_simp [hR.ne'] <;> ring
  have hleft (x : ℝ) (hx : A x < 0) : θ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hAC.continuousAt.eventually (Iio_mem_nhds hx)] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  have hright (x : ℝ) (hx : 1 < A x) : θ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hAC.continuousAt.eventually (Ioi_mem_nhds hx)] with y hy
    exact smoothTransition.one_of_one_le hy.le
  have hAleft (x : ℝ) (hx : x ≤ a) : A x < 0 := by
    have h := hAmono.monotone hx
    rw [hAa] at h
    linarith
  have hAright (x : ℝ) (hx : b ≤ x) : 1 < A x := by
    have h := hAmono.monotone hx
    rw [hAb] at h
    linarith
  have hθ : ContDiff ℝ ∞ θ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ Ioo a b
    · have hsc := (tailResistanceChart_contDiffOn hp hpos hps).contDiffAt
        (isOpen_Ioo.mem_nhds hx)
      exact smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_const.mul hsc).sub contDiffAt_const)
    · rcases le_or_gt x a with hxa | hax
      · exact contDiffAt_const.congr_of_eventuallyEq (hleft x (hAleft x hxa))
      · have hbx : b ≤ x := le_of_not_gt (fun hxb => hx ⟨hax, hxb⟩)
        exact contDiffAt_const.congr_of_eventuallyEq (hright x (hAright x hbx))
  have hsupport : tsupport (deriv θ) ⊆ Ioo a b := by
    have hc : IsClosed {x : ℝ | 0 ≤ A x ∧ A x ≤ 1} :=
      (isClosed_le continuous_const hAC).inter (isClosed_le hAC continuous_const)
    have hder : Function.support (deriv θ) ⊆ {x : ℝ | 0 ≤ A x ∧ A x ≤ 1} := by
      intro x hx
      constructor
      · by_contra hn
        have he := (hleft x (lt_of_not_ge hn)).deriv_eq
        exact hx (by simpa only [deriv_const] using he)
      · by_contra hn
        have he := (hright x (lt_of_not_ge hn)).deriv_eq
        exact hx (by simpa only [deriv_const] using he)
    apply (closure_minimal hder hc).trans
    intro x hx
    constructor
    · by_contra hn
      exact (not_lt_of_ge hx.1) (hAleft x (le_of_not_gt hn))
    · by_contra hn
      exact (not_lt_of_ge hx.2) (hAright x (le_of_not_gt hn))
  have hderiv (x : ℝ) : deriv θ x = deriv smoothTransition (A x) * ((2 / R) * (p x)⁻¹) := by
    exact (((smoothTransition.contDiff : ContDiff ℝ ∞ smoothTransition).differentiable
      (by simp) (A x)).hasDerivAt.comp x
      (((hasDerivAt_tailResistanceChart hp hpos a x).const_mul (2 / R)).sub_const (1 / 2))).deriv
  have henergy (x : ℝ) :
      p x * deriv θ x ^ 2 ≤ (4 * (M + 1) ^ 2 / R ^ 2) * (p x)⁻¹ := by
    have hb : (deriv smoothTransition (A x)) ^ 2 ≤ (M + 1) ^ 2 := by
      have hu := (abs_le.mp (hbound (A x))).2
      have hl := (abs_le.mp (hbound (A x))).1
      have hmul : 0 ≤ (M - deriv smoothTransition (A x)) *
          (M + deriv smoothTransition (A x)) :=
        mul_nonneg (sub_nonneg.mpr hu) (by linarith)
      nlinarith
    rw [hderiv]
    have hid : p x * (deriv smoothTransition (A x) * ((2 / R) * (p x)⁻¹)) ^ 2 =
        (4 / R ^ 2) * (p x)⁻¹ * (deriv smoothTransition (A x)) ^ 2 := by
      field_simp [(hpos x).ne', hR.ne'] <;> ring
    rw [hid]
    calc
      _ ≤ (4 / R ^ 2) * (p x)⁻¹ * (M + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
          (inv_nonneg.mpr (hpos x).le))
      _ = _ := by ring
  have hE : (∫ x in a..b, p x * deriv θ x ^ 2) ≤ 4 * (M + 1) ^ 2 / R := by
    have hi₁ : IntervalIntegrable (fun x => p x * deriv θ x ^ 2) volume a b :=
      (hp.mul (((contDiff_infty_iff_deriv.mp hθ).2.continuous).pow 2)).intervalIntegrable a b
    have hi₂ : IntervalIntegrable (fun x => (4 * (M + 1) ^ 2 / R ^ 2) * (p x)⁻¹)
        volume a b :=
      (continuous_const.mul (hp.inv₀ (fun x => (hpos x).ne'))).intervalIntegrable a b
    calc
      _ ≤ ∫ x in a..b, (4 * (M + 1) ^ 2 / R ^ 2) * (p x)⁻¹ :=
        intervalIntegral.integral_mono_on hab.le hi₁ hi₂ (fun x _ => henergy x)
      _ = (4 * (M + 1) ^ 2 / R ^ 2) * R := by
        rw [intervalIntegral.integral_const_mul]
        rfl
      _ = _ := by field_simp [hR.ne'] <;> ring
  exact ⟨hθ, fun x => ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩,
    fun x hx => smoothTransition.zero_of_nonpos (hAleft x hx).le,
    fun x hx => smoothTransition.one_of_one_le (hAright x hx).le,
    hleft a (hAleft a le_rfl), hright b (hAright b le_rfl), hsupport, hE⟩

/-- The clamped extension is used only to define the coordinate outside the
edge. It agrees with the original density everywhere on the closed edge. -/
def tailClampedDensity (p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : ℝ → ℝ :=
  IccExtend hab (fun x : Icc a b => p x)

theorem tailClampedDensity_eq {p : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b) :
    tailClampedDensity p a b hab x = p x :=
  IccExtend_of_mem hab _ hx

theorem exists_tailSmoothResistanceStep :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ → ℝ) (a b : ℝ), a < b →
      ContDiffOn ℝ ∞ p (Icc a b) → (∀ x ∈ Icc a b, 0 < p x) →
      ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧
        (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
        (∀ x, x ≤ a → θ x = 0) ∧ (∀ x, b ≤ x → θ x = 1) ∧
        (θ =ᶠ[𝓝 a] fun _ => 0) ∧ (θ =ᶠ[𝓝 b] fun _ => 1) ∧
        tsupport (deriv θ) ⊆ Ioo a b ∧
        (∫ x in a..b, p x * deriv θ x ^ 2) ≤ C / (∫ x in a..b, (p x)⁻¹) := by
  obtain ⟨M, hM, hb⟩ := tail_transition_derivative_bound
  refine ⟨4 * (M + 1) ^ 2, by positivity, ?_⟩
  intro p a b hab hp hpos
  let q : ℝ → ℝ := tailClampedDensity p a b hab.le
  have hq : Continuous q := (continuousOn_iff_continuous_domRestrict.mp hp.continuousOn).Icc_extend'
  have hqp : ∀ x, 0 < q x := by
    intro x
    dsimp only [q]
    rw [tailClampedDensity, IccExtend_apply]
    exact hpos _ ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
  have hqeq (x : ℝ) (hx : x ∈ Icc a b) : q x = p x :=
    tailClampedDensity_eq hab.le hx
  have hqs : ContDiffOn ℝ ∞ q (Ioo a b) := by
    apply (hp.mono Ioo_subset_Icc_self).congr
    intro x hx
    exact tailClampedDensity_eq hab.le ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hθ, hrange, hleft, hright, hca, hcb, hs, hE⟩ :=
    tailSmoothResistanceStep_spec hab hq hqp hqs hM hb
  refine ⟨tailSmoothResistanceStep q a b, hθ, hrange, hleft, hright, hca, hcb, hs, ?_⟩
  have hμ : (∫ x in a..b, (q x)⁻¹) = ∫ x in a..b, (p x)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (fun r : ℝ => r⁻¹)
      (hqeq x (by simpa only [uIcc_of_le hab.le] using hx))
  have he : (∫ x in a..b, p x * deriv (tailSmoothResistanceStep q a b) x ^ 2) =
      ∫ x in a..b, q x * deriv (tailSmoothResistanceStep q a b) x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (fun r : ℝ => r * deriv (tailSmoothResistanceStep q a b) x ^ 2)
      (hqeq x (by simpa only [uIcc_of_le hab.le] using hx)).symm
  rw [he, ← hμ]
  exact hE

end ContinuousFlexibility.Radial
