import ContinuousFlexibility.Analysis.N04NegativeChartPointFlowBounds
import ContinuousFlexibility.Analysis.RootInverseNormalizedBounds
import ContinuousFlexibility.Analysis.PeriodicScalarFlow
import ContinuousFlexibility.Analysis.N01cOpticalNumericEnvelopes

/-! Finite ordinary bounds for the same chosen flow on physical radial fibers. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem field_fiber_raw_bounds {F : ℝ × N04FlowPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hp : ∀ t v, Function.Periodic (fun θ => F (t, (v, θ))) Real.pi)
    (v : ℝ × ℝ) :
    ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ j t, t ∈ Icc (0 : ℝ) 1 → ∀ θ,
      ‖iteratedFDeriv ℝ (j + 1) (fun q => F (t, q)) (v, θ)‖ ≤ M j := by
  classical
  have hs : ContDiff ℝ ∞ (fun z : N04FlowPoint × ℝ => F (z.2, z.1)) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hex (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
      ‖iteratedFDeriv ℝ (j + 1) (fun q => F (t, q)) (v, θ)‖ ≤ M := by
    apply exists_norm_bound_periodic_compact isCompact_Icc Real.pi_ne_zero
    · exact ((contDiff_parametricSpatialJet hs (j + 1)).continuous.comp
        ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)).continuousOn
    · intro t ht θ
      have he : (fun q : N04FlowPoint => F (t, ((0 : ℝ × ℝ), Real.pi) + q)) =
          (fun q => F (t, q)) := by
        funext q
        simpa only [Prod.mk_add_mk, zero_add, add_comm Real.pi q.2] using hp t q.1 q.2
      have hh := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun q : N04FlowPoint => F (t, q)) (j + 1)
        ((0 : ℝ × ℝ), Real.pi) (v, θ)
      rw [he] at hh
      simpa only [Prod.mk_add_mk, zero_add, add_comm Real.pi θ] using hh.symm
  choose M hM hb using hex
  exact ⟨M, hM, hb⟩

/-- The unused higher bounds are consequences of smoothness and
periodicity. Only the displayed finite prefix enters the polynomial. -/
theorem n04NegativeChart_flow_point_prefix (N : ℕ) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {M ρ : ℝ}, 1 ≤ M → 1 ≤ ρ →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ => F (t, (v, θ))) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ q : N04FlowPoint,
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ θ, |deriv (fun η => F (t, (q.1, η))) θ| ≤ 1) →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
        ‖iteratedFDeriv ℝ (j + 1) (fun y => F (t, y)) (q.1, θ)‖ ≤ M * ρ ^ j) →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (k + 1) (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
          C * M ^ e * ρ ^ k := by
  obtain ⟨C, e, hC, hb⟩ := n04NegativeChart_flow_spatial_point_weighted_prefix 1 N
  refine ⟨C, e, hC, ?_⟩
  intro M ρ hM hρ F hF hp Θ hΘ q hangle hraw
  obtain ⟨R, hR, hr⟩ := field_fiber_raw_bounds hF hp q.1
  exact hb hM hρ F hF hp Θ hΘ q R hR hr (fun _ => 1)
    continuousOn_const (fun _ _ => zero_le_one) hangle
    (by simp only [intervalIntegral.integral_const, sub_zero, one_smul, le_refl]) hraw

def negativeChartLowInputBound (C : ℝ) (e : ℕ) (M : ℝ) : ℝ :=
  let B := 1 + M + Real.pi + C * M ^ e
  8 * (M + B + 1) * B ^ 2

theorem negativeChartLowInputBound_envelope {I : Type*} {E M : I → ℝ}
    (hE : ∀ i, 1 ≤ E i) (hM : ∀ i, 1 ≤ M i) (hb : HasPositiveEnvelope E M)
    (C : ℝ) (hC : 1 ≤ C) (e : ℕ) :
    HasPositiveEnvelope E (fun i => negativeChartLowInputBound C e (M i)) := by
  have hpow := hb.pow hE (fun i => zero_le_one.trans (hM i)) e
  have hB := (((hasPositiveEnvelope_const E hE 1).add hE hb).add hE
    (hasPositiveEnvelope_const E hE Real.pi)).add hE
      ((hasPositiveEnvelope_const E hE C).mul hE hpow
        (fun i => pow_nonneg (zero_le_one.trans (hM i)) _))
  have hB0 (i : I) : 0 ≤ 1 + M i + Real.pi + C * M i ^ e := by
    have hi := hM i
    have hc := hC
    positivity
  exact ((hasPositiveEnvelope_const E hE 8).mul hE
    ((hb.add hE hB).add hE (hasPositiveEnvelope_const E hE 1))
    (fun i => by have hi := hM i; have hbi := hB0 i; positivity)).mul hE
      (hB.pow hE hB0 2) (fun _ => sq_nonneg _)

private theorem displacement_jet_to_value {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) {n : ℕ} {θ : ℝ}
    (hθ : |θ| ≤ R) (hb : ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤ M) :
    ‖iteratedFDeriv ℝ n h θ‖ ≤ M + R + 1 := by
  have hid : ‖iteratedFDeriv ℝ n (id : ℝ → ℝ) θ‖ ≤ R + 1 := by
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero, id_eq, Real.norm_eq_abs] using
        hθ.trans (le_add_of_nonneg_right zero_le_one)
    | succ n => exact (flowJet_norm_iteratedFDeriv_clm_le
        (ContinuousLinearMap.id ℝ ℝ) (Nat.succ_pos n) θ).trans
          ((ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)).trans
            (le_add_of_nonneg_left hR))
  have he : h = (fun η => h η - η) + id := by funext η; simp
  conv_lhs => rw [he]
  rw [iteratedFDeriv_add_apply
    ((hh.sub contDiff_id).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) contDiffAt_id]
  exact (norm_add_le _ _).trans ((add_le_add hb hid).trans_eq (by ring))

/-- The estimate is on the positive radial box. Smooth extensions only
supply existence of unused higher derivatives. The chosen flow is retained. -/
theorem n04NegativeChart_normalized_flow_low :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ => F (t, (v, θ))) Real.pi) →
      (∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox → 0 ≤ q.1.1 →
        ∀ t ∈ Icc (0 : ℝ) 1,
          |deriv (fun η => F (t, (q.1, η))) q.2| ≤ 1) →
      (∀ j, j ≤ 2 → ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox → 0 ≤ q.1.1 →
        ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ j (fun y => F (t, y)) q‖ ≤ M) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
      (∀ j, j ≤ 2 → ∀ θ, ‖iteratedFDeriv ℝ j (fun η => h η - η) θ‖ ≤ M) →
      ∀ σ : ℝ, |σ| ≤ 1 →
        CSBound 2 (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
          (h ∘ ((fun q : N04FlowPoint => Θ q.1 1 q.2) ∘ rootFlowNormalizedArgument σ))
          (negativeChartLowInputBound C e M) := by
  obtain ⟨C, e, hC, hb⟩ := n04NegativeChart_flow_point_prefix 1
  refine ⟨C, e, hC, ?_⟩
  intro M hM F hF hp hangle hraw Θ hΘ h hh hl σ hσ n hn q hq
  let g : N04FlowPoint → ℝ := fun y => Θ y.1 1 y.2
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hg : ContDiff ℝ ∞ g := n04Flow_contDiff_slice hF hp hΘ ht
  let v := rootFlowNormalizedArgument σ q
  have hv : v.1 ∈ n04FlowParameterBox := by
    rw [rootFlowNormalizedArgument_apply]
    refine ⟨⟨(by linarith only [hq.1.1]), hq.1.2⟩, ?_⟩
    exact abs_le.mp ((by rw [abs_mul]; exact mul_le_mul hσ
      (abs_le.mpr hq.2.1) (abs_nonneg _) zero_le_one : |σ * q.2.1| ≤ 1 * 1).trans_eq
      (one_mul 1))
  have hvx : 0 ≤ v.1.1 := hq.1.1
  have hvθ : |v.2| ≤ Real.pi := abs_le.mpr hq.2.2
  let B : ℝ := 1 + M + Real.pi + C * M ^ e
  have hterm : 0 ≤ C * M ^ e :=
    mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _)
  have hB : 1 ≤ B := by
    dsimp only [B]
    linarith only [hM, Real.pi_pos, hterm]
  have hvalue : |g v| ≤ M + Real.pi := by
    have hb0 := n04Flow_displacement_abs_le hF hΘ v.1 v.2 (zero_le_one.trans hM)
      (fun t ht θ => by simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        hraw 0 (by omega) (v.1, θ) hv hvx t ht) ht
    calc
      _ = |(g v - v.2) + v.2| := by rw [sub_add_cancel]
      _ ≤ |g v - v.2| + |v.2| := abs_add_le _ _
      _ ≤ _ := add_le_add hb0 hvθ
  have hjet (k : ℕ) (hk : k ≤ 2) : ‖iteratedFDeriv ℝ k g v‖ ≤ B := by
    cases k with
    | zero =>
        simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact hvalue.trans (by dsimp only [B]; linarith only [hterm])
    | succ k =>
        have hh := hb hM (le_refl (1 : ℝ)) F hF hp Θ hΘ v
          (fun t ht θ => hangle (v.1, θ) hv hvx t ht)
          (fun j hj t ht θ => by simpa only [one_pow, mul_one] using
            hraw (j + 1) (by omega) (v.1, θ) hv hvx t ht)
          k (by omega) 1 ht
        exact (by simpa only [one_pow, mul_one] using hh :
          ‖iteratedFDeriv ℝ (k + 1) g v‖ ≤ C * M ^ e).trans
          (by dsimp only [B]; linarith only [hM, Real.pi_pos])
  have hin (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (g ∘ rootFlowNormalizedArgument σ) q‖ ≤ 2 * B := by
    have hc := norm_iteratedFDeriv_comp_le hg (rootFlowNormalizedArgument σ).contDiff
      (by simp : (k : ℕ∞ω) ≤ ∞) q (C := B) (D := (1 : ℝ))
      (fun j hj => hjet j (hj.trans hk))
      (fun j hj _ => by simpa only [one_pow] using
        (flowJet_norm_iteratedFDeriv_clm_le (rootFlowNormalizedArgument σ) hj q).trans
          (rootFlowNormalizedArgument_norm hσ))
    have hf : (k.factorial : ℝ) ≤ 2 := by interval_cases k <;> norm_num
    exact (by simpa only [one_pow, mul_one] using hc :
      ‖iteratedFDeriv ℝ k (g ∘ rootFlowNormalizedArgument σ) q‖ ≤ k.factorial * B).trans
      (mul_le_mul_of_nonneg_right hf (zero_le_one.trans hB))
  have houter (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k h ((g ∘ rootFlowNormalizedArgument σ) q)‖ ≤ M + B + 1 :=
    displacement_jet_to_value hh (zero_le_one.trans hM) (zero_le_one.trans hB)
      (hvalue.trans (by dsimp only [B]; linarith only [hterm]))
      (hl k (hk.trans hn) _)
  have h2B : 1 ≤ 2 * B := by linarith only [hB]
  have hcomp := norm_iteratedFDeriv_comp_le hh (hg.comp (rootFlowNormalizedArgument σ).contDiff)
    (by simp : (n : ℕ∞ω) ≤ ∞) q (C := M + B + 1) (D := 2 * B) houter
    (fun k hk hkn => (hin k (hkn.trans hn)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ h2B hk))
  have hfact : (n.factorial : ℝ) ≤ 2 := by interval_cases n <;> norm_num
  calc
    _ ≤ n.factorial * (M + B + 1) * (2 * B) ^ n := hcomp
    _ ≤ 2 * (M + B + 1) * (2 * B) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfact (by positivity))
        (pow_le_pow_right₀ h2B hn) (pow_nonneg (by positivity) _) (by positivity)
    _ = _ := by dsimp only [negativeChartLowInputBound, B]; ring

end ContinuousFlexibility.Analysis
