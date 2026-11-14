module

public import ContinuousFlexibility.Radial.R07DeepTailBounds

/-!
# A uniformly valid deep tail for each fixed physical frequency

The depth may depend on the frequency and the fixed realized geometry.
It is chosen before the height sequence. The natural solution obtained
there can subsequently be continued across the finitely many preceding
cells to any prescribed transition entrance.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_deepTail_mass_nonneg {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) (n : ℕ) :
    0 ≤ tailMass (r07DeepTailData T D right j start η K) n := by
  have ho := r07_deepTail_interval_order h right j hstart η K n
  have hb := r07_deepTail_node_bounds h right j hstart η K n
  have hp := (r07_deepTail_density_properties h right j hstart η K).2
  apply intervalIntegral.integral_nonneg ho.1.le
  intro x hx
  exact (hp x ⟨hb.1.trans hx.1, hx.2.trans_lt hb.2.2⟩).le

theorem r07_deepTail_hypotheses {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) {η K : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (hsmall : (162 * exp 2 * ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * (C 0) ^ 2) *
      exp (-(start : ℝ)) ≤ η)
    (hratio : ((exp 2 * (C 0) ^ 2) * exp (-(start : ℝ))) ≤ η)
    (hbig : K ≤ (exp (-2) * ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) / (C 0) ^ 2) *
      exp (start : ℝ)) :
    DeepTailHypotheses (r07DeepTailData T D right j start η K) := by
  let Q := r07DeepTailData T D right j start η K
  have hΛ : 0 < Q.Λ := r07_deepTail_lambda_pos hj
  have hden := r07_deepTail_density_properties h right j hstart η K
  have hnode := r07_deepTail_node_bounds h right j hstart η K 0
  have hmass (n : ℕ) : 0 ≤ tailMass Q n := r07_deepTail_mass_nonneg h right j hstart η K n
  refine ⟨r07_deepTail_entrance_lt_endpoint h right j hstart η K, hnode.1, hΛ, ?_,
    hη, hη1, hK, hden.1, hden.2, r07_deepTail_nodes_tendsto h right j hstart η K, ?_⟩
  · cases right
    · have hi := r07_deepTail_initial_bounds h hσ hb hj hstart h32 η K hclose
      refine Or.inr ⟨r07_deepTail_initial_order h false j hstart η K,
        hi.1.trans hsmall, ?_, hbig.trans hi.2.2⟩
      exact hi.2.1.trans (mul_le_mul_of_nonneg_right hratio (hmass 0))
    · exact Or.inl (r07_deepTail_initial_order h true j hstart η K).symm
  · intro n
    have ho := r07_deepTail_interval_order h right j hstart η K n
    have hs := r07_deepTail_small_products h hσ hb right hj hstart h32 η K hclose n
    have hn := r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K hclose n n (Or.inl rfl)
    have hnext := r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K hclose
      n (n + 1) (Or.inr rfl)
    have hcast : (start : ℝ) ≤ ((start + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right start n
    have hexp := exp_le_exp.mpr (neg_le_neg hcast)
    have hsmalln : (162 * exp 2 * Q.Λ * (C 0) ^ 2) *
        exp (-((start + n : ℕ) : ℝ)) ≤ η :=
      (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hsmall
    have hratn : (exp 2 * (C 0) ^ 2) * exp (-((start + n : ℕ) : ℝ)) ≤ η :=
      (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hratio
    have hbign : K ≤ (exp (-2) * Q.Λ / (C 0) ^ 2) * exp ((start + n : ℕ) : ℝ) :=
      hbig.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hcast) (by positivity))
    refine ⟨ho.1, ho.2, hs.trans hsmalln, hbign.trans hn.1, hbign.trans hnext.1, ?_⟩
    change tailGapMass Q n ≤ η * min (tailMass Q n) (tailMass Q (n + 1))
    rw [mul_min_of_nonneg _ _ hη.le]
    exact le_min
      (hn.2.1.trans (mul_le_mul_of_nonneg_right hratn (hmass n)))
      (hnext.2.1.trans (mul_le_mul_of_nonneg_right hratn (hmass (n + 1))))

theorem r07_deepTail_entrances_tendsto {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) (η K : ℝ) :
    Tendsto (fun start => (r07DeepTailData T D right j start η K).entrance) atTop
      (𝓝 (r07OutwardLog right (if right then D.b else D.a))) := by
  have hD := r07_realization_geometry h
  cases right
  · have hl := (h.2.2.2.2.2.2.1 false).1.comp (tendsto_sub_atTop_nat 1)
    have hr : Tendsto (fun n => morseChainResistanceEnd T false n) atTop (𝓝 D.a) := by
      apply hl.congr'
      filter_upwards [eventually_gt_atTop T.index] with n hn
      have hprev : T.index ≤ n - 1 := by omega
      have he := (r07_chain_resistance_ends h hprev).2
      have hn1 : 1 ≤ n := by omega
      simpa only [Function.comp_def, Nat.sub_add_cancel hn1] using he.symm
    exact (hr.log hD.1.ne').neg
  · exact ((h.2.2.2.2.2.2.1 true).1.log (hD.1.trans hD.2.1).ne')

/-- For every fixed frequency, a single depth works for the entire height
cube and both endpoints. All deep hypotheses are obtained from the actual
realized profiles and their mass/resistance bounds. -/
theorem r07_exists_uniform_deepTailHypotheses
    (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization T σ (family σ) C ∧ MorseMassResistanceBounds T σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b)
    {j : ℕ} (hj : 2 ≤ j) {η K : ℝ} (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K)
    (minimum : ℕ) :
    ∃ start : ℕ, minimum ≤ start ∧ T.index < start ∧ 32 ≤ start ∧
      ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → ∀ right : Bool,
        let Q := r07DeepTailData T (family σ) right j start η K
        Q.endpoint - Q.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ ∧ DeepTailHypotheses Q := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  let D₀ := family σ₀
  let Λ : ℝ := (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)
  have hσ₀ : ∀ k, 1 ≤ σ₀ k ∧ σ₀ k ≤ 2 := fun _ => ⟨le_rfl, by norm_num [σ₀]⟩
  have h₀ := (hfamily σ₀ hσ₀).1
  have hC : 0 < C 0 := h₀.constants_pos 0
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : 0 < (j : ℝ) := by linarith only [hj']
  have hj2 : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith only [sq_nonneg ((j : ℝ) - 2), hj']
  have hΛ : 0 < Λ := mul_pos (pow_pos hjp 2) (by linarith only [hj2])
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hcast)
  have hsmallLim : Tendsto (fun n : ℕ => (162 * exp 2 * Λ * (C 0) ^ 2) * exp (-(n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := 162 * exp 2 * Λ * (C 0) ^ 2)).mul hdecay
  have hratioLim : Tendsto (fun n : ℕ => (exp 2 * (C 0) ^ 2) * exp (-(n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := exp 2 * (C 0) ^ 2)).mul hdecay
  have hbigLim : Tendsto (fun n : ℕ => (exp (-2) * Λ / (C 0) ^ 2) * exp (n : ℝ))
      atTop atTop := (tendsto_exp_atTop.comp hcast).const_mul_atTop (by positivity)
  have hclose : ∀ᶠ n : ℕ in atTop, ∀ right : Bool,
      (r07DeepTailData T D₀ right j n η K).endpoint -
        (r07DeepTailData T D₀ right j n η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ := by
    apply eventually_all.mpr
    intro right
    have he := r07_deepTail_entrances_tendsto h₀ right j η K
    have hd : Tendsto (fun n => (r07DeepTailData T D₀ right j n η K).endpoint -
        (r07DeepTailData T D₀ right j n η K).entrance) atTop (𝓝 0) := by
      simpa only [D₀, r07DeepTailData, sub_self] using
        (tendsto_const_nhds (x := r07OutwardLog right (if right then D₀.b else D₀.a))).sub he
    exact (hd.eventually (eventually_lt_nhds (by positivity : 0 < (2 * (j : ℝ) ^ 2)⁻¹))).mono
      (fun _ hn => hn.le)
  obtain ⟨start, hmin, hstart, h32, hc, hs, hr, hb⟩ :=
    ((eventually_ge_atTop minimum).and ((eventually_gt_atTop T.index).and ((eventually_ge_atTop (32 : ℕ)).and
      (hclose.and ((hsmallLim.eventually (eventually_lt_nhds hη)).and
        ((hratioLim.eventually (eventually_lt_nhds hη)).and
          (hbigLim.eventually (eventually_ge_atTop K)))))))).exists
  refine ⟨start, hmin, hstart, h32, ?_⟩
  intro σ hσ right
  have hreal := (hfamily σ hσ).1
  have hmass := (hfamily σ hσ).2
  have hEnd := hends σ σ₀
  have hcloseσ : (r07DeepTailData T (family σ) right j start η K).endpoint -
      (r07DeepTailData T (family σ) right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ := by
    simpa only [r07DeepTailData, hEnd.1, hEnd.2] using hc right
  exact ⟨hcloseσ, r07_deepTail_hypotheses hreal hσ hmass right hj hstart h32 hη hη1 hK
    hcloseσ hs.le hr.le hb⟩

end ContinuousFlexibility.Radial
