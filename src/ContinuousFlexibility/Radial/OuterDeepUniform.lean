import ContinuousFlexibility.Radial.OuterDeepActionHypotheses
import ContinuousFlexibility.Radial.OuterDeepCutoff
import ContinuousFlexibility.Radial.R07DeepTailPhysical

/-!
# One actual deep tail for the entire moving frequency band

The cutoff is chosen before the height sequence, frequency and endpoint.
Fine action estimates control the small products, while the existing R07
large-product and mass-ratio bounds have frequency-independent thresholds.
The final data are the actual outer factory at the geometrical entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

/-- The actual R07 tail satisfies the full deep and physical predicates
throughout every sufficiently deep upper frequency band. The same cutoff
works for the whole height cube and both orientations. -/
theorem outer_eventually_uniform_deepTailPhysical
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar η K : ℝ} (hCstar : 0 < Cstar)
    (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
        ∀ right : Bool,
          let Q := r07DeepTailData M (family σ) right j (n + 1) η K
          Q.endpoint - Q.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ ∧
            DeepTailHypotheses Q ∧
              TailPhysicalRelation (family σ) Q right j (n + 1) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have hσ₀ : ∀ k, 1 ≤ σ₀ k ∧ σ₀ k ≤ 2 :=
    fun _ => ⟨le_rfl, by norm_num [σ₀]⟩
  have h₀ := (hfamily σ₀ hσ₀).1
  have hC : 0 < C 0 := h₀.constants_pos 0
  have hlog : 0 < log (4 : ℝ) := log_pos (by norm_num)
  let L : ℝ := exp 2 * (C 0) ^ 2 * (1 + (log 4)⁻¹)
  have hL : 0 < L := by dsimp only [L]; positivity
  let ε : ℝ := min 1 (η / (L + 1))
  have hLp : 0 < L + 1 := by linarith only [hL]
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hη hLp)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / (L + 1) := min_le_right _ _
  have hεsq : ε ^ 2 ≤ ε := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hε1 hε.le
  have hbudget : exp 2 * (C 0) ^ 2 * ε ^ 2 * (1 + (log 4)⁻¹) ≤ η := by
    calc
      _ = L * ε ^ 2 := by dsimp only [L]; ring
      _ ≤ L * ε := mul_le_mul_of_nonneg_left hεsq hL.le
      _ ≤ (L + 1) * ε :=
        mul_le_mul_of_nonneg_right (by linarith) hε.le
      _ ≤ η := by
        simpa only [mul_comm] using (le_div_iff₀ hLp).mp hεη
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hcast)
  have hratioLim : Tendsto
      (fun n : ℕ => (exp 2 * (C 0) ^ 2) * exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := exp 2 * (C 0) ^ 2)).mul hdecay
  have hbigLim : Tendsto
      (fun n : ℕ => (exp (-2) / (C 0) ^ 2) * exp (n : ℝ)) atTop atTop :=
    (tendsto_exp_atTop.comp hcast).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop M.index, eventually_ge_atTop (31 : ℕ),
      morseTransition_eventually_deep_of_upper M hCstar
        (fun k hk => h₀.d_eq k hk) hε,
      morseTransition_eventually_deepTail_close h₀ hCstar,
      hratioLim.eventually (eventually_lt_nhds hη),
      hbigLim.eventually (eventually_ge_atTop K)] with n hn h31 ha hc hr hb
  intro σ hσ j hj hjupper right
  have hreal := (hfamily σ hσ).1
  have hmass := (hfamily σ hσ).2
  have hstart : M.index < n + 1 := hn.trans_lt (Nat.lt_succ_self n)
  have h32 : 32 ≤ n + 1 := by omega
  have hEnd := hends σ σ₀
  have hclose : (r07DeepTailData M (family σ) right j (n + 1) η K).endpoint -
      (r07DeepTailData M (family σ) right j (n + 1) η K).entrance ≤
        (2 * (j : ℝ) ^ 2)⁻¹ := by
    simpa only [r07DeepTailData, hEnd.1, hEnd.2] using hc j hj hjupper right η K
  have haction : ∀ m, n + 1 ≤ m → (j : ℝ) ^ 2 * morseChainA M m *
      sqrt (log (morseChainA M m / morseChainB M m)) ≤ ε := by
    intro m hm
    exact (ha j hn hjupper m (by omega)).le
  have hncast : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  have hratio : exp 2 * (C 0) ^ 2 * exp (-((n + 1 : ℕ) : ℝ)) ≤ η :=
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hncast))
      (by positivity)).trans hr.le
  have hbig : K ≤ (exp (-2) / (C 0) ^ 2) * exp ((n + 1 : ℕ) : ℝ) :=
    hb.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hncast) (by positivity))
  exact ⟨hclose, outer_deepTail_hypotheses_of_action hreal hσ hmass right
    hj hstart h32 hη hη1 hK hclose haction hbudget hratio hbig,
    r07_deepTail_physical_relation hreal hσ hmass right hj hstart h32 η K hclose⟩

/-- A single geometrical cutoff gives the full R06 predicates for the
actual outer factory, for every later index and every frequency below
its moving upper threshold. This includes all low frequencies in the
new initial band; no lower band hypothesis is imposed. -/
theorem outer_exists_uniform_actual_deepTailPhysical
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar η K : ℝ} (hCstar : 0 < Cstar)
    (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K) (minimum : ℕ) :
    ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index ≤ N₀ ∧ 31 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
        ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
          ∀ right : Bool,
            let Q := morsePhysicalDeepTail M (family σ) right j (n + 1)
              (morseOuterDeepEntrance M right n) η K
            Q.endpoint - Q.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ ∧
              DeepTailHypotheses Q ∧
                TailPhysicalRelation (family σ) Q right j (n + 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (outer_eventually_uniform_deepTailPhysical M C family hfamily hends hCstar hη hη1 hK)
  let N₀ := max N (max minimum (max M.index 31))
  have hmin : minimum ≤ N₀ := by dsimp only [N₀]; omega
  have hidx : M.index ≤ N₀ := by dsimp only [N₀]; omega
  have h31 : 31 ≤ N₀ := by dsimp only [N₀]; omega
  refine ⟨N₀, hmin, hidx, h31, ?_⟩
  intro n hn σ hσ j hj hjupper right
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hnidx : M.index ≤ n := hidx.trans hn
  dsimp only
  rw [morsePhysicalDeepTail_eq_r07 (hfamily σ hσ).1 right j n hnidx η K]
  exact hN n hNn σ hσ j hj hjupper right

end ContinuousFlexibility.Radial
