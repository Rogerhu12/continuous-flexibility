import ContinuousFlexibility.Analysis.IntervalWeakRegularity

/-!
# Energy identities from actual conormal primitives

The weak equation is still tested only against smooth functions in the
regularity theorem. Once the actual flux primitive has been constructed,
Fubini permits C¹ compact tests. Applying this to `χ² u` gives the local
energy identity needed for Caccioppoli estimates.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- The integral of the derivative of an interior C¹ compact test is zero. -/
theorem integral_deriv_eq_zero_of_compact_Ioo {a b : ℝ} (hab : a < b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) : (∫ x, deriv ψ x) = 0 := by
  obtain ⟨l, r, _hal, _hlr, _hrb, hs⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hψc hψs
  have hsd : Function.support (deriv ψ) ⊆ Ioc l r := by
    intro x hx
    have hx' := hs (support_deriv_subset hx)
    exact ⟨hx'.1, hx'.2.le⟩
  have hψl : ψ l = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => (lt_irrefl l) (hs hh).1)
  have hψr : ψ r = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => (lt_irrefl r) (hs hh).2)
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsd,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hψ.differentiable (by simp) x)
      ((hψ.continuous_deriv le_rfl).intervalIntegrable _ _), hψr, hψl, sub_self]

/-- An actual primitive flux can be tested against compact C¹ functions. -/
theorem integral_flux_mul_deriv_eq_neg_Ioo {a b : ℝ} (hab : a < b)
    {h F : ℝ → ℝ} (hh : LocallyIntegrableOn h (Ioo a b) volume)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b) (q : ℝ)
    (hF : ∀ x ∈ Ioo a b, F x = intervalLocalPrimitive h x₀ x + q)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, F x * deriv ψ x) = -(∫ x, h x * ψ x) := by
  have hHcont := continuousOn_intervalLocalPrimitive hab hh hx₀
  have hHloc := hHcont.locallyIntegrableOn measurableSet_Ioo
  have hψd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψds : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hψs
  have hHi : Integrable (fun x => intervalLocalPrimitive h x₀ x * deriv ψ x) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hHloc hψd hψc.deriv hψds
  have hψdi : Integrable (deriv ψ) :=
    hψd.integrable_of_hasCompactSupport hψc.deriv
  have hfun : (fun x => F x * deriv ψ x) =
      (fun x => intervalLocalPrimitive h x₀ x * deriv ψ x + q * deriv ψ x) := by
    funext x
    by_cases hx : x ∈ Ioo a b
    · rw [hF x hx, add_mul]
    · have hdx : deriv ψ x = 0 :=
        deriv_of_notMem_tsupport (fun hh' => hx (hψs hh'))
      simp only [hdx, mul_zero, add_zero]
  rw [hfun, integral_add hHi (hψdi.const_mul q), integral_const_mul,
    integral_deriv_eq_zero_of_compact_Ioo hab hψ hψc hψs, mul_zero, add_zero]
  exact integral_intervalLocalPrimitive_mul_deriv_Ioo_of_contDiff_one hab hh hx₀
    hψ hψc hψs

theorem continuousOn_deriv_of_contDiffOn_one_Ioo {a b : ℝ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioo a b)) : ContinuousOn (deriv u) (Ioo a b) := by
  have hu' : ContDiffOn ℝ (0 + 1) u (Ioo a b) := by simpa only [zero_add] using hu
  exact ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mp hu').2.2.continuousOn

/-- The cutoff square times an interior C¹ field is a genuine global C¹
compact test. -/
theorem interval_cutoff_square_mul_test {a b : ℝ} {u χ : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioo a b)) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo a b) :
    ContDiff ℝ 1 (fun x => χ x ^ 2 * u x) ∧
      HasCompactSupport (fun x => χ x ^ 2 * u x) ∧
      tsupport (fun x => χ x ^ 2 * u x) ⊆ Ioo a b := by
  have hsupp : Function.support (fun x => χ x ^ 2 * u x) ⊆ tsupport χ := by
    intro x hx
    change χ x ^ 2 * u x ≠ 0 at hx
    by_contra hxχ
    exact hx (by rw [image_eq_zero_of_notMem_tsupport hxχ, zero_pow (by decide), zero_mul])
  have hts : tsupport (fun x => χ x ^ 2 * u x) ⊆ Ioo a b :=
    (closure_minimal hsupp (isClosed_tsupport χ)).trans hχs
  exact ⟨contDiff_of_contDiffOn_of_tsupport_subset isOpen_Ioo
    (((hχ.of_le (by simp) : ContDiff ℝ 1 χ).contDiffOn.pow 2).mul hu) hts,
    hχc.mono' hsupp, hts⟩

/-- Testing the actual conormal primitive with `χ²u` gives the full local
energy identity, without requiring a classical second derivative. -/
theorem interval_cutoff_energy_identity {a b : ℝ} (hab : a < b)
    {u w h χ : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hw : ContinuousOn w (Ioo a b))
    (hh : LocallyIntegrableOn h (Ioo a b) volume)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b) (q : ℝ)
    (hflux : ∀ x ∈ Ioo a b,
      w x * deriv u x = intervalLocalPrimitive h x₀ x + q) :
    (∫ x, w x * χ x ^ 2 * deriv u x ^ 2) =
      -(∫ x, h x * (χ x ^ 2 * u x)) -
        2 * (∫ x, w x * χ x * deriv χ x * u x * deriv u x) := by
  have hud : ContinuousOn (deriv u) (Ioo a b) := continuousOn_deriv_of_contDiffOn_one_Ioo hu
  have hχd : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  let ψ : ℝ → ℝ := fun x => χ x ^ 2 * u x
  obtain ⟨hψ, hψc, hψs⟩ := interval_cutoff_square_mul_test hu hχ hχc hχs
  have hψder (x : ℝ) :
      deriv ψ x = 2 * χ x * deriv χ x * u x + χ x ^ 2 * deriv u x := by
    by_cases hx : x ∈ Ioo a b
    · have hux : DifferentiableAt ℝ u x :=
        (hu.differentiableOn (by simp) x hx).differentiableAt
          (isOpen_Ioo.mem_nhds hx)
      have hr := (((hχ.differentiable (by simp) x).hasDerivAt).pow 2).mul hux.hasDerivAt
      simpa only [ψ, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hr.deriv
    · have hdx : deriv ψ x = 0 :=
        deriv_of_notMem_tsupport (fun hh' => hx (hψs hh'))
      have hχx : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh' => hx (hχs hh'))
      rw [hdx, hχx]
      ring
  have hEcore : ContinuousOn (fun x => w x * χ x * deriv u x ^ 2) (Ioo a b) :=
    (hw.mul hχ.continuous.continuousOn).mul (hud.pow 2)
  have hEi : Integrable (fun x => w x * χ x ^ 2 * deriv u x ^ 2) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hEcore.locallyIntegrableOn measurableSet_Ioo) hχ.continuous hχc hχs
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hXcore : ContinuousOn
      (fun x => w x * deriv χ x * u x * deriv u x) (Ioo a b) :=
    ((hw.mul hχd.continuousOn).mul hu.continuousOn).mul hud
  have hXi : Integrable (fun x => w x * χ x * deriv χ x * u x * deriv u x) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hXcore.locallyIntegrableOn measurableSet_Ioo) hχ.continuous hχc hχs
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hweak :=
    integral_flux_mul_deriv_eq_neg_Ioo hab hh x₀ hx₀ q hflux hψ hψc hψs
  change (∫ x, (w x * deriv u x) * deriv ψ x) = -(∫ x, h x * ψ x) at hweak
  have hfun : (fun x => (w x * deriv u x) * deriv ψ x) =
      (fun x => w x * χ x ^ 2 * deriv u x ^ 2 +
        2 * (w x * χ x * deriv χ x * u x * deriv u x)) := by
    funext x
    rw [hψder]
    ring
  rw [hfun, integral_add hEi (hXi.const_mul 2), integral_const_mul] at hweak
  change (∫ x, w x * χ x ^ 2 * deriv u x ^ 2) +
      2 * (∫ x, w x * χ x * deriv χ x * u x * deriv u x) =
    -(∫ x, h x * (χ x ^ 2 * u x)) at hweak
  linarith

end

end ContinuousFlexibility.Analysis
