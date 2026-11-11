import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weak primitives on an open real interval

A smooth test of integral zero supported strictly inside an interval is the
derivative of another smooth test supported strictly inside the same interval.
Consequently, a locally integrable function whose first distributional
derivative vanishes is almost everywhere constant on the entire interval.

All integrals in the first theorem are ordinary Lebesgue integrals on the
real line. The final theorem also accepts integrals over the open interval.
The hypotheses do not impose integrability at either endpoint.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- A compact subset of an open real interval lies in a smaller closed
interval. The two endpoints are treated together. -/
private theorem weakPrimitive_compact_inner_interval {a b : ℝ} (hab : a < b)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo a b) :
    ∃ l r : ℝ, a < l ∧ l < r ∧ r < b ∧ K ⊆ Ioo l r := by
  rcases K.eq_empty_or_nonempty with hzero | hne
  · refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · simp [hzero]
  · obtain ⟨p, hp, hmin⟩ :=
      hK.exists_isMinOn hne (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) K)
    obtain ⟨q, hq, hmax⟩ :=
      hK.exists_isMaxOn hne (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) K)
    have hap : a < p := (hKI hp).1
    have hqb : q < b := (hKI hq).2
    have hpq : p ≤ q := hmin hq
    refine ⟨(a + p) / 2, (q + b) / 2, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · intro x hx
      have hpx : p ≤ x := hmin hx
      have hxq : x ≤ q := hmax hx
      constructor <;> linarith

/-- A smooth compactly supported test of integral zero has a smooth compact
primitive. The primitive remains strictly inside the original interval. -/
theorem exists_contDiff_compactPrimitive_Ioo {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioo a b) (hfi : (∫ x, f x) = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo a b ∧ deriv φ = f := by
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ :=
    weakPrimitive_compact_inner_interval hab hfc hfs
  let φ : ℝ → ℝ := fun x => ∫ y in l..x, f y
  have hd (x : ℝ) : HasDerivAt φ (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  have hder : deriv φ = f := funext fun x => (hd x).deriv
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hd x).differentiableAt, ?_⟩
    rw [hder]
    exact hf
  have hleft (x : ℝ) (hx : x < l) : φ x = 0 := by
    change (∫ y in l..x, f y) = 0
    rw [intervalIntegral.integral_of_ge hx.le]
    have hz : (∫ y in Ioc x l, f y) = 0 := by
      calc
        (∫ y in Ioc x l, f y) = ∫ _y in Ioc x l, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro y hy
          exact image_eq_zero_of_notMem_tsupport
            (fun hyf => (not_lt_of_ge hy.2) (hs hyf).1)
        _ = 0 := by simp
    rw [hz, neg_zero]
  have hright (x : ℝ) (hx : r < x) : φ x = 0 := by
    change (∫ y in l..x, f y) = 0
    rw [intervalIntegral.integral_eq_integral_of_support_subset, hfi]
    intro y hy
    have hy' := hs (subset_tsupport f hy)
    exact ⟨hy'.1, hy'.2.le.trans hx.le⟩
  have hsupport : Function.support φ ⊆ Icc l r := by
    intro x hx
    change φ x ≠ 0 at hx
    constructor
    · by_contra hxl
      exact hx (hleft x (lt_of_not_ge hxl))
    · by_contra hxr
      exact hx (hright x (lt_of_not_ge hxr))
  have htsupport : tsupport φ ⊆ Icc l r :=
    closure_minimal hsupport isClosed_Icc
  refine ⟨φ, hφ,
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport, ?_, hder⟩
  intro x hx
  exact ⟨hal.trans_le (htsupport hx).1, (htsupport hx).2.trans_lt hrb⟩

/-- A unit-integral smooth test strictly inside an arbitrary nonempty bounded
open interval. -/
theorem exists_contDiff_unitIntegral_Ioo {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∫ x, ρ x) = 1 := by
  let c : ℝ := (a + b) / 2
  let η : ContDiffBump c :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨η.normed volume, η.contDiff_normed, η.hasCompactSupport_normed, ?_,
    η.integral_normed⟩
  rw [η.tsupport_normed_eq]
  intro x hx
  have hdist : |x - c| ≤ (b - a) / 4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, η] using hx
  have hlo := (abs_le.mp hdist).1
  have hhi := (abs_le.mp hdist).2
  dsimp [c] at hlo hhi
  constructor <;> linarith

/-- Multiplication by a continuous test supported compactly inside an interval
turns local integrability into global integrability. -/
theorem integrable_mul_test_of_locallyIntegrableOn_Ioo {a b : ℝ}
    {u ψ : ℝ → ℝ} (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    Integrable (fun x => u x * ψ x) := by
  have hi : IntegrableOn u (tsupport ψ) :=
    hu.integrableOn_compact_subset hψs hψc
  have hp : IntegrableOn (fun x => u x * ψ x) (tsupport ψ) :=
    hi.mul_continuousOn hψ.continuousOn hψc
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).mp hp
  intro x hx
  change u x * ψ x ≠ 0 at hx
  by_contra hxψ
  exact hx (by rw [image_eq_zero_of_notMem_tsupport hxψ, mul_zero])

/-- Vanishing distributional first derivative implies constancy almost
everywhere on the whole open interval. No endpoint integrability is assumed. -/
theorem exists_ae_eq_const_of_integral_mul_deriv_eq_zero_Ioo {a b : ℝ}
    (hab : a < b) {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, u x * deriv φ x) = 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] (fun _ => c) := by
  obtain ⟨ρ, hρ, hρc, hρs, hρint⟩ := exists_contDiff_unitIntegral_Ioo hab
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have huρ : Integrable (fun x => u x * ρ x) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hu hρ.continuous hρc hρs
  let c : ℝ := ∫ x, u x * ρ x
  have hpair (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ Ioo a b) :
      (∫ x, u x * ψ x) = (∫ x, ψ x) * c := by
    let A : ℝ := ∫ x, ψ x
    let k : ℝ → ℝ := fun x => ψ x - A * ρ x
    have hk : ContDiff ℝ ∞ k := hψ.sub (contDiff_const.mul hρ)
    have hksupport : Function.support k ⊆ tsupport ψ ∪ tsupport ρ := by
      intro x hx
      change ψ x - A * ρ x ≠ 0 at hx
      by_contra hmem
      have hxψ : x ∉ tsupport ψ := fun hh => hmem (Or.inl hh)
      have hxρ : x ∉ tsupport ρ := fun hh => hmem (Or.inr hh)
      exact hx (by rw [image_eq_zero_of_notMem_tsupport hxψ,
        image_eq_zero_of_notMem_tsupport hxρ, mul_zero, sub_zero])
    have hkts : tsupport k ⊆ tsupport ψ ∪ tsupport ρ :=
      closure_minimal hksupport ((isClosed_tsupport ψ).union (isClosed_tsupport ρ))
    have hkc : HasCompactSupport k :=
      HasCompactSupport.of_support_subset_isCompact (hψc.isCompact.union hρc.isCompact)
        hksupport
    have hks : tsupport k ⊆ Ioo a b := by
      intro x hx
      exact (hkts hx).elim hψs hρs
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hki : (∫ x, k x) = 0 := by
      dsimp only [k]
      rw [integral_sub hψi (hρi.const_mul A), integral_const_mul, hρint, mul_one]
      exact sub_self A
    obtain ⟨φ, hφ, hφc, hφs, hder⟩ :=
      exists_contDiff_compactPrimitive_Ioo hab hk hkc hks hki
    have htest := hw φ hφ hφc hφs
    have huψ : Integrable (fun x => u x * ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψ.continuous hψc hψs
    have hprod : (fun x => u x * k x) =
        (fun x => u x * ψ x - A * (u x * ρ x)) := by
      funext x
      dsimp only [k]
      ring
    rw [hder, hprod, integral_sub huψ (huρ.const_mul A), integral_const_mul] at htest
    exact sub_eq_zero.mp htest
  have hc : LocallyIntegrableOn (fun _ : ℝ => c) (Ioo a b) volume :=
    continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioo
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo a b → u x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hu.sub hc)
    intro ψ hψ hψc hψs
    change (∫ x, ψ x • (u x - c)) = 0
    have huψ : Integrable (fun x => u x * ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψ.continuous hψc hψs
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have heq : (fun x => ψ x • (u x - c)) =
        (fun x => u x * ψ x - c * ψ x) := by
      funext x
      simp only [smul_eq_mul]
      ring
    rw [heq, integral_sub huψ (hψi.const_mul c), integral_const_mul,
      hpair ψ hψ hψc hψs]
    ring
  refine ⟨c, ?_⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hz] with x hx hxin
  exact sub_eq_zero.mp (hx hxin)

/-- The same conclusion when the weak derivative is expressed with the
restricted interval measure. -/
theorem exists_ae_eq_const_of_setIntegral_mul_deriv_eq_zero_Ioo {a b : ℝ}
    (hab : a < b) {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x in Ioo a b, u x * deriv φ x) = 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] (fun _ => c) := by
  apply exists_ae_eq_const_of_integral_mul_deriv_eq_zero_Ioo hab hu
  intro φ hφ hφc hφs
  have he : (∫ x in Ioo a b, u x * deriv φ x) = ∫ x, u x * deriv φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxφ : x ∉ tsupport φ := fun hh => hx (hφs hh)
    have hzero : φ =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxφ] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hder : deriv φ x = 0 := by
      rw [hzero.deriv_eq]
      exact deriv_const x 0
    rw [hder, mul_zero]
  rw [← he]
  exact hw φ hφ hφc hφs

/-- Two locally integrable representatives with the same distributional first
derivative differ by a single constant on the connected interval. -/
theorem exists_ae_eq_add_const_of_integral_sub_mul_deriv_eq_zero_Ioo {a b : ℝ}
    (hab : a < b) {u v : ℝ → ℝ}
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hv : LocallyIntegrableOn v (Ioo a b) volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, (u x - v x) * deriv φ x) = 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] (fun x => v x + c) := by
  obtain ⟨c, hc⟩ :=
    exists_ae_eq_const_of_integral_mul_deriv_eq_zero_Ioo hab (hu.sub hv) hw
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change u x - v x = c at hx
  linarith

end

end ContinuousFlexibility.Analysis
