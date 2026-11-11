import ContinuousFlexibility.Analysis.IntervalL1Primitive
import ContinuousFlexibility.Analysis.FlatExtension
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Zero endpoint traces from integrable derivatives and reciprocal-distance weights

An integrable actual derivative gives a continuous extension by the genuine
Lebesgue primitive.  Integrability after division by the distance to an
endpoint forces that extension's endpoint value to vanish.  This reduces
smooth flat extension to integral estimates for actual ordinary derivatives.
The same trace lemma treats either endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem continuousAt_eq_zero_of_integrable_div_sub
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    {u v : ℝ → ℝ} (hv : ContinuousAt v c) (he : EqOn u v (Ioo a b))
    (hi : IntegrableOn (fun x => u x / (x - c)) (Ioo a b)) :
    v c = 0 := by
  by_contra hn
  have hvc : 0 < |v c| := abs_pos.mpr hn
  have hnear : {x : ℝ | |v c| / 2 < |v x|} ∈ 𝓝 c :=
    hv.abs.eventually (Ioi_mem_nhds (by linarith : |v c| / 2 < |v c|))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let p : ℝ := max a (c - ε / 2)
  let q : ℝ := min b (c + ε / 2)
  have hpq : p < q := by
    dsimp only [p, q]
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hab, by linarith [hc.1]⟩, ⟨by linarith [hc.2], by linarith⟩⟩
  have hpc : p ≤ c := max_le hc.1 (by linarith)
  have hcq : c ≤ q := le_min hc.2 (by linarith)
  have hsub : Ioo p q ⊆ Ioo a b := by
    intro x hx
    exact ⟨(le_max_left a _).trans_lt hx.1, hx.2.trans_le (min_le_left b _)⟩
  have hbound (x : ℝ) (hx : x ∈ Ioo p q) :
      1 ≤ (2 / |v c|) * |u x| := by
    have hxc : dist x c < ε := by
      rw [Real.dist_eq, abs_lt]
      have hp : c - ε / 2 < x := (le_max_right a _).trans_lt hx.1
      have hq : x < c + ε / 2 := hx.2.trans_le (min_le_right b _)
      constructor <;> linarith
    have hb : |v c| / 2 < |v x| := hball hxc
    rw [he (hsub hx)]
    have hr : (2 / |v c|) * |v x| = (2 * |v x|) / |v c| := by ring
    rw [hr]
    exact (le_div_iff₀ hvc).mpr (by linarith)
  have hinv : IntegrableOn (fun x => (x - c)⁻¹) (Ioo p q) := by
    apply ((hi.mono_set hsub).norm.const_mul (2 / |v c|)).mono'
      (((measurable_id.sub measurable_const).inv).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hb := mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg ((x - c)⁻¹))
    simpa only [one_mul, Real.norm_eq_abs, div_eq_mul_inv, abs_mul, mul_assoc] using hb
  have hinterval : IntervalIntegrable (fun x => (x - c)⁻¹) volume p q :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hpq.le).mpr hinv
  rcases intervalIntegrable_sub_inv_iff.mp hinterval with heq | hnot
  · exact hpq.ne heq
  · exact hnot (by simpa only [uIcc_of_le hpq.le] using (show c ∈ Icc p q from ⟨hpc, hcq⟩))

theorem exists_continuous_extension_of_integrable_deriv {a b : ℝ}
    {u d : ℝ → ℝ}
    (hd : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hdc : ContinuousOn d (Ioo a b))
    (hdi : IntegrableOn d (Ioo a b)) :
    ∃ v : ℝ → ℝ, Continuous v ∧ EqOn u v (Ioo a b) := by
  let P : ℝ → ℝ := intervalL1Primitive a b d
  have hPc : Continuous P := continuous_intervalL1Primitive hdi
  have hPd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt P (d x) x :=
    hasDerivAt_intervalL1Primitive_of_ae_eq hdi Filter.EventuallyEq.rfl hdc hx
  have hdiff : DifferentiableOn ℝ (fun x => u x - P x) (Ioo a b) :=
    fun x hx => ((hd x hx).sub (hPd x hx)).differentiableAt.differentiableWithinAt
  have hzero (x : ℝ) (hx : x ∈ Ioo a b) :
      deriv (fun y => u y - P y) x = 0 := by
    simpa only [sub_self] using ((hd x hx).sub (hPd x hx)).deriv
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hdiff hzero
  refine ⟨fun x => P x + c, hPc.add continuous_const, fun x hx => ?_⟩
  have he := hc x hx
  change u x - P x = c at he
  linarith

theorem endpoint_limits_zero_of_integrable_div {a b : ℝ} (hab : a < b)
    {u d : ℝ → ℝ}
    (hd : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hdc : ContinuousOn d (Ioo a b))
    (hdi : IntegrableOn d (Ioo a b))
    (hleft : IntegrableOn (fun x => u x / (x - a)) (Ioo a b))
    (hright : IntegrableOn (fun x => u x / (x - b)) (Ioo a b)) :
    Tendsto u (𝓝[>] a) (𝓝 0) ∧ Tendsto u (𝓝[<] b) (𝓝 0) := by
  obtain ⟨v, hv, huv⟩ := exists_continuous_extension_of_integrable_deriv hd hdc hdi
  have hva : v a = 0 :=
    continuousAt_eq_zero_of_integrable_div_sub hab ⟨le_rfl, hab.le⟩ hv.continuousAt huv hleft
  have hvb : v b = 0 :=
    continuousAt_eq_zero_of_integrable_div_sub hab ⟨hab.le, le_rfl⟩ hv.continuousAt huv hright
  constructor
  · have ht := (hv.tendsto a).mono_left nhdsWithin_le_nhds
    rw [hva] at ht
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (huv hx).symm
  · have ht := (hv.tendsto b).mono_left nhdsWithin_le_nhds
    rw [hvb] at ht
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (huv hx).symm

theorem contDiff_zero_extension_of_integrable_jets {a b : ℝ} (hab : a < b)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ ∞ u (Ioo a b))
    (hi : ∀ s : ℕ, IntegrableOn (iteratedDeriv s u) (Ioo a b))
    (hleft : ∀ s : ℕ,
      IntegrableOn (fun x => iteratedDeriv s u x / (x - a)) (Ioo a b))
    (hright : ∀ s : ℕ,
      IntegrableOn (fun x => iteratedDeriv s u x / (x - b)) (Ioo a b)) :
    ContDiff ℝ ∞ (extendZeroOutside a b u) := by
  have hlim (s : ℕ) :
      Tendsto (iteratedDeriv s u) (𝓝[>] a) (𝓝 0) ∧
        Tendsto (iteratedDeriv s u) (𝓝[<] b) (𝓝 0) := by
    apply endpoint_limits_zero_of_integrable_div hab
      (d := iteratedDeriv (s + 1) u) _ _ (hi (s + 1)) (hleft s) (hright s)
    · intro x hx
      have hd := ((differentiableOn_iteratedDeriv_Ioo hu s x hx).differentiableAt
        (isOpen_Ioo.mem_nhds hx)).hasDerivAt
      simpa only [iteratedDeriv_succ] using hd
    · exact (differentiableOn_iteratedDeriv_Ioo hu (s + 1)).continuousOn
  exact contDiff_extendZeroOutside hab hu (fun s => (hlim s).1) (fun s => (hlim s).2)

end ContinuousFlexibility.Analysis
