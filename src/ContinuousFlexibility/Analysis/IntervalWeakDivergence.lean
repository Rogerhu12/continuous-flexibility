import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp

/-!
# Homogeneous weak divergence equations on an interval

For a smooth coefficient which does not vanish in an open interval, the
distributional equation `(w * u')' = 0` has only the usual two-dimensional
family of solutions. The proof factors compact tests through the smooth
primitive of a test of integral zero. No ODE existence theorem or
distribution-valued derivative is needed.

The coefficient may vanish at the endpoints. All regularity assertions are
local to the open interval.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- Smoothness on an open set extends globally for a function whose
topological support lies in that open set. -/
theorem contDiff_of_contDiffOn_of_tsupport_subset {n : ℕ∞ω} {s : Set ℝ} (hs : IsOpen s)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f s) (hfs : tsupport f ⊆ s) :
    ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hs.mem_nhds (hfs hx))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy

/-- Dividing an interior smooth test by a coefficient which is nonzero on
the open set preserves global smoothness, including outside the open set. -/
theorem contDiff_div_of_tsupport_subset {n : ℕ∞ω} {s : Set ℝ} (hs : IsOpen s)
    {f w : ℝ → ℝ} (hf : ContDiff ℝ n f) (hw : ContDiffOn ℝ n w s)
    (hwn : ∀ x ∈ s, w x ≠ 0) (hfs : tsupport f ⊆ s) :
    ContDiff ℝ n (fun x => f x / w x) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset hs (hf.contDiffOn.div hw hwn)
  have hsub : tsupport (fun x => f x / w x) ⊆ tsupport f := by
    simpa only [div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := f) (g := fun x => (w x)⁻¹))
  exact hsub.trans hfs

private theorem weakDivergence_compact_div {f w : ℝ → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (fun x => f x / w x) := by
  apply hf.mono'
  intro x hx
  change f x / w x ≠ 0 at hx
  by_contra hxf
  exact hx (by rw [image_eq_zero_of_notMem_tsupport hxf, zero_div])

private theorem weakDivergence_tsupport_div {f w : ℝ → ℝ} :
    tsupport (fun x => f x / w x) ⊆ tsupport f := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := f) (g := fun x => (w x)⁻¹))

/-- The homogeneous second-order weak equation first reduces to a single
constant reciprocal-coefficient first derivative. -/
theorem exists_reciprocal_pairing_of_divergence_eq_zero_Ioo {a b : ℝ}
    (hab : a < b) {w u : ℝ → ℝ} (hw : ContDiffOn ℝ ∞ w (Ioo a b))
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = 0) :
    ∃ q : ℝ, ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
        (∫ x, u x * deriv ψ x) = (∫ x, ψ x / w x) * q := by
  obtain ⟨ρ, hρ, hρc, hρs, hρint⟩ := exists_contDiff_unitIntegral_Ioo hab
  let η : ℝ → ℝ := fun x => w x * ρ x
  have hηs : tsupport η ⊆ Ioo a b :=
    tsupport_mul_subset_right.trans hρs
  have hη : ContDiff ℝ ∞ η :=
    contDiff_of_contDiffOn_of_tsupport_subset isOpen_Ioo (hw.mul hρ.contDiffOn) hηs
  have hηc : HasCompactSupport η := hρc.mul_left
  have hηquot : (fun x => η x / w x) = ρ := by
    funext x
    by_cases hx : x ∈ Ioo a b
    · dsimp only [η]
      field_simp [hwn x hx]
    · have hρx : ρ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx (hρs hh))
      simp [η, hρx]
  have hηd : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have huη : Integrable (fun x => u x * deriv η x) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hu hηd.continuous hηc.deriv
      (tsupport_deriv_subset.trans hηs)
  let q : ℝ := ∫ x, u x * deriv η x
  refine ⟨q, ?_⟩
  intro ψ hψ hψc hψs
  let A : ℝ := ∫ x, ψ x / w x
  let k : ℝ → ℝ := fun x => ψ x - A * η x
  have hk : ContDiff ℝ ∞ k := hψ.sub (contDiff_const.mul hη)
  have hAηc : HasCompactSupport (fun x => A * η x) := hηc.mul_left
  have hkc : HasCompactSupport k := hψc.sub hAηc
  have hks : tsupport k ⊆ Ioo a b := by
    intro x hx
    rcases tsupport_sub ψ (fun y => A * η y) hx with hxψ | hxη
    · exact hψs hxψ
    · exact hηs (tsupport_mul_subset_right hxη)
  have hg : ContDiff ℝ ∞ (fun x => k x / w x) :=
    contDiff_div_of_tsupport_subset isOpen_Ioo hk hw hwn hks
  have hgc : HasCompactSupport (fun x => k x / w x) :=
    weakDivergence_compact_div hkc
  have hgs : tsupport (fun x => k x / w x) ⊆ Ioo a b :=
    weakDivergence_tsupport_div.trans hks
  have hψquot : ContDiff ℝ ∞ (fun x => ψ x / w x) :=
    contDiff_div_of_tsupport_subset isOpen_Ioo hψ hw hwn hψs
  have hψqi : Integrable (fun x => ψ x / w x) :=
    hψquot.continuous.integrable_of_hasCompactSupport (weakDivergence_compact_div hψc)
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hgformula : (fun x => k x / w x) = (fun x => ψ x / w x - A * ρ x) := by
    funext x
    dsimp only [k]
    rw [sub_div, mul_div_assoc, congrFun hηquot x]
  have hgi : (∫ x, k x / w x) = 0 := by
    rw [hgformula, integral_sub hψqi (hρi.const_mul A), integral_const_mul,
      hρint, mul_one]
    exact sub_self A
  obtain ⟨φ, hφ, hφc, hφs, hφder⟩ :=
    exists_contDiff_compactPrimitive_Ioo hab hg hgc hgs hgi
  have hwφ : (fun x => w x * deriv φ x) = k := by
    funext x
    rw [congrFun hφder x]
    by_cases hx : x ∈ Ioo a b
    · field_simp [hwn x hx]
    · have hkx : k x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx (hks hh))
      simp [hkx]
  have hkd : deriv k = fun x => deriv ψ x - A * deriv η x := by
    funext x
    exact ((hψ.differentiable (by simp) x).hasDerivAt.sub
      ((hη.differentiable (by simp) x).hasDerivAt.const_mul A)).deriv
  have htest := hdiv φ hφ hφc hφs
  rw [hwφ, hkd] at htest
  have hψd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have huψ : Integrable (fun x => u x * deriv ψ x) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψd.continuous hψc.deriv
      (tsupport_deriv_subset.trans hψs)
  have hfun : (fun x => u x * (deriv ψ x - A * deriv η x)) =
      (fun x => u x * deriv ψ x - A * (u x * deriv η x)) := by
    funext x
    ring
  rw [hfun, integral_sub huψ (huη.const_mul A), integral_const_mul] at htest
  exact sub_eq_zero.mp htest

/-- Classical integration by parts against a strictly interior test requires
only the displayed local derivative and its continuity. -/
theorem integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b)
    {P d : ℝ → ℝ} (hP : ∀ x ∈ Ioo a b, HasDerivAt P (d x) x)
    (hd : ContinuousOn d (Ioo a b)) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, P x * deriv ψ x) = -(∫ x, d x * ψ x) := by
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hψc hψs
  have hsub : uIcc l r ⊆ Ioo a b := by
    rw [uIcc_of_le hlr.le]
    intro x hx
    exact ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  have hdi : IntervalIntegrable d volume l r := (hd.mono hsub).intervalIntegrable
  have hψdi : IntervalIntegrable (deriv ψ) volume l r :=
    (contDiff_infty_iff_deriv.mp hψ).2.continuous.intervalIntegrable _ _
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := l) (b := r) (u := P) (v := ψ) (u' := d) (v' := deriv ψ)
    (fun x hx => hP x (hsub hx))
    (fun x (_hx : x ∈ uIcc l r) => (hψ.differentiable (by simp) x).hasDerivAt)
    hdi hψdi
  have hψl : ψ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl l) (hs hh).1)
  have hψr : ψ r = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl r) (hs hh).2)
  rw [hψr, hψl, mul_zero, mul_zero, sub_self, zero_sub] at hip
  have hsleft : Function.support (fun x => P x * deriv ψ x) ⊆ Ioc l r := by
    intro x hx
    have hdx : deriv ψ x ≠ 0 := by
      intro hz
      apply hx
      change P x * deriv ψ x = 0
      rw [hz, mul_zero]
    have hxψ := hs (support_deriv_subset hdx)
    exact ⟨hxψ.1, hxψ.2.le⟩
  have hsright : Function.support (fun x => d x * ψ x) ⊆ Ioc l r := by
    intro x hx
    have hpx : ψ x ≠ 0 := by
      intro hz
      apply hx
      change d x * ψ x = 0
      rw [hz, mul_zero]
    have hxψ := hs (subset_tsupport ψ hpx)
    exact ⟨hxψ.1, hxψ.2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsleft,
    intervalIntegral.integral_eq_integral_of_support_subset hsright] at hip
  exact hip

/-- Relative to any actual reciprocal-coefficient primitive, a homogeneous
weak divergence solution is affine in that primitive almost everywhere. -/
theorem exists_ae_eq_affine_primitive_of_divergence_eq_zero_Ioo {a b : ℝ}
    (hab : a < b) {w u P : ℝ → ℝ} (hw : ContDiffOn ℝ ∞ w (Ioo a b))
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hP : ∀ x ∈ Ioo a b, HasDerivAt P ((w x)⁻¹) x)
    (hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = 0) :
    ∃ c q : ℝ, u =ᵐ[volume.restrict (Ioo a b)] (fun x => c + q * P x) := by
  obtain ⟨q, hq⟩ :=
    exists_reciprocal_pairing_of_divergence_eq_zero_Ioo hab hw hwn hu hdiv
  have hPc : ContinuousOn P (Ioo a b) :=
    fun x hx => (hP x hx).continuousAt.continuousWithinAt
  have hPi : LocallyIntegrableOn P (Ioo a b) volume :=
    hPc.locallyIntegrableOn measurableSet_Ioo
  have hv : LocallyIntegrableOn (fun x => u x + q * P x) (Ioo a b) volume :=
    hu.add ((continuousOn_const.mul hPc).locallyIntegrableOn measurableSet_Ioo)
  have hwInv : ContinuousOn (fun x => (w x)⁻¹) (Ioo a b) :=
    (hw.inv hwn).continuousOn
  have hvw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
        (∫ x, (u x + q * P x) * deriv ψ x) = 0 := by
    intro ψ hψ hψc hψs
    have hψd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
    have hψds : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hψs
    have huψ : Integrable (fun x => u x * deriv ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψd.continuous hψc.deriv hψds
    have hPψ : Integrable (fun x => P x * deriv ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hPi hψd.continuous hψc.deriv hψds
    have hip := integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo hab hP hwInv hψ hψc hψs
    have hquot : (fun x => (w x)⁻¹ * ψ x) = (fun x => ψ x / w x) := by
      funext x
      simp only [div_eq_mul_inv, mul_comm]
    rw [hquot] at hip
    have hfun : (fun x => (u x + q * P x) * deriv ψ x) =
        (fun x => u x * deriv ψ x + q * (P x * deriv ψ x)) := by
      funext x
      ring
    rw [hfun, integral_add huψ (hPψ.const_mul q), integral_const_mul,
      hq ψ hψ hψc hψs, hip]
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_mul_deriv_eq_zero_Ioo hab hv hvw
  refine ⟨c, -q, ?_⟩
  filter_upwards [hc] with x hx
  change u x + q * P x = c at hx
  linarith

/-- The explicit reciprocal-coefficient primitive used for homogeneous
one-dimensional divergence equations. -/
def intervalReciprocalPrimitive (w : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  ∫ y in x₀..x, (w y)⁻¹

theorem hasDerivAt_intervalReciprocalPrimitive {a b : ℝ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    HasDerivAt (intervalReciprocalPrimitive w x₀) ((w x)⁻¹) x := by
  have hsub : uIcc x₀ x ⊆ Ioo a b := by
    intro y hy
    exact ⟨(lt_min hx₀.1 hx.1).trans_le hy.1,
      hy.2.trans_lt (max_lt hx₀.2 hx.2)⟩
  have hi : IntervalIntegrable (fun y => (w y)⁻¹) volume x₀ x :=
    (((hw.contDiffOn.inv hwn).continuousOn).mono hsub).intervalIntegrable
  have hm : AEStronglyMeasurable (fun y => (w y)⁻¹) (volume : Measure ℝ) :=
    hw.continuous.measurable.inv.aestronglyMeasurable
  exact intervalIntegral.integral_hasDerivAt_right hi
    hm.stronglyMeasurableAtFilter (hw.contDiffAt.inv (hwn x hx)).continuousAt

/-- The full homogeneous weak divergence classification with its explicit
integral representative. -/
theorem exists_ae_eq_affine_reciprocalPrimitive_of_divergence_eq_zero_Ioo
    {a b : ℝ} (hab : a < b) {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = 0) :
    ∃ c q : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      (fun x => c + q * intervalReciprocalPrimitive w x₀ x) :=
  exists_ae_eq_affine_primitive_of_divergence_eq_zero_Ioo hab hw.contDiffOn hwn hu
    (fun x hx => hasDerivAt_intervalReciprocalPrimitive hw hwn hx₀ hx) hdiv

end

end ContinuousFlexibility.Analysis
