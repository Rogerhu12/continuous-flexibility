module

public import ContinuousFlexibility.Analysis.N06H2Approximation
public import ContinuousFlexibility.Analysis.N06WeightedLpLimits
public import ContinuousFlexibility.Analysis.N06DegenerateGraph
public import ContinuousFlexibility.Statements.N06Parts

/-!
# The positive-cylinder graph estimate for actual weak solutions

Closed-interval regularity supplies the same almost-everywhere representative.
Its H2 approximation transfers the smooth estimate, with precisely the same
constant and without imposing endpoint conditions on the original solution.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The smooth estimate passes to a C1 representative whose first derivative is
absolutely continuous and whose actual second derivative belongs to L2. -/
theorem n06_regular_cubic_graph_bound {a v c V q F : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hv : ContDiff ℝ 1 v)
    (hvdAC : AbsolutelyContinuousOnInterval (deriv v) 0 1)
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hv₀ : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hF : MemLp F 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hode : ∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1),
      -(a y * deriv (deriv v) y + deriv a y * deriv v y) +
        j ^ 2 * c y * v y + V y * v y = F y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv v y) ^ 2) +
      (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * v y ^ 2) +
      (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv v) y) ^ 2) +
      (1 + j ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * v y ^ 2) +
      (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv v y ^ 2) ≤
      16384 * K ^ 10 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
        ∫ y in (0 : ℝ)..1, v y ^ 2) := by
  obtain ⟨p, hp, hp₀, hp₁, hp₂, hlim₀, hlim₁, hlim₂⟩ :=
    n06_exists_smooth_H2_approximation hv hvdAC hv₀ hv₁ hv₂
  let p₂ : ℝ → ℝ := fun y => -a y
  let p₁ : ℝ → ℝ := fun y => -deriv a y
  let p₀ : ℝ → ℝ := fun y => j ^ 2 * c y + V y
  have hc₂ : Continuous p₂ := ha.continuous.neg
  have hc₁' : Continuous p₁ := (ha.continuous_deriv le_rfl).neg
  have hc₀ : Continuous p₀ := (continuous_const.mul hc).add hV
  have hm₂ (n : ℕ) : MemLp (p₂ * deriv (deriv (p n))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous (hp₂ n) hc₂
  have hm₁ (n : ℕ) : MemLp (p₁ * deriv (p n)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous (hp₁ n) hc₁'
  have hm₀ (n : ℕ) : MemLp (p₀ * p n) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous (hp₀ n) hc₀
  have hn₂ : MemLp (p₂ * deriv (deriv v)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous hv₂ hc₂
  have hn₁ : MemLp (p₁ * deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous hv₁ hc₁'
  have hn₀ : MemLp (p₀ * v) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    n06_interval_memLp_mul_continuous hv₀ hc₀
  let Fn : ℕ → ℝ → ℝ :=
    fun n => p₂ * deriv (deriv (p n)) + p₁ * deriv (p n) + p₀ * p n
  let T : ℝ → ℝ := p₂ * deriv (deriv v) + p₁ * deriv v + p₀ * v
  have hFn (n : ℕ) : MemLp (Fn n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((hm₂ n).add (hm₁ n)).add (hm₀ n)
  have hT : MemLp T 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hn₂.add hn₁).add hn₀
  have hTF : T =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] F := by
    filter_upwards [hode] with y hy
    dsimp only [T, p₂, p₁, p₀, Pi.add_apply, Pi.mul_apply]
    nlinarith only [hy]
  have hFn_sum (n : ℕ) : (hFn n).toLp (Fn n) =
      (hm₂ n).toLp (p₂ * deriv (deriv (p n))) +
        (hm₁ n).toLp (p₁ * deriv (p n)) + (hm₀ n).toLp (p₀ * p n) := by
    change (((hm₂ n).add (hm₁ n)).add (hm₀ n)).toLp
      (p₂ * deriv (deriv (p n)) + p₁ * deriv (p n) + p₀ * p n) = _
    rw [MemLp.toLp_add ((hm₂ n).add (hm₁ n)) (hm₀ n),
      MemLp.toLp_add (hm₂ n) (hm₁ n)]
  have hT_sum : hT.toLp T = hn₂.toLp (p₂ * deriv (deriv v)) +
      hn₁.toLp (p₁ * deriv v) + hn₀.toLp (p₀ * v) := by
    change ((hn₂.add hn₁).add hn₀).toLp
      (p₂ * deriv (deriv v) + p₁ * deriv v + p₀ * v) = _
    rw [MemLp.toLp_add (hn₂.add hn₁) hn₀, MemLp.toLp_add hn₂ hn₁]
  have hFlim : Tendsto (fun n => (hFn n).toLp (Fn n)) atTop (𝓝 (hF.toLp F)) := by
    have h₂ := n06_tendsto_unit_toLp_mul_continuous hp₂ hv₂ hc₂ hlim₂
    have h₁ := n06_tendsto_unit_toLp_mul_continuous hp₁ hv₁ hc₁' hlim₁
    have h₀ := n06_tendsto_unit_toLp_mul_continuous hp₀ hv₀ hc₀ hlim₀
    have hsum := (h₂.add h₁).add h₀
    change Tendsto (fun n =>
      (hm₂ n).toLp (p₂ * deriv (deriv (p n))) +
        (hm₁ n).toLp (p₁ * deriv (p n)) + (hm₀ n).toLp (p₀ * p n)) atTop
      (𝓝 (hn₂.toLp (p₂ * deriv (deriv v)) + hn₁.toLp (p₁ * deriv v) +
        hn₀.toLp (p₀ * v))) at hsum
    have hTeq : hT.toLp T = hF.toLp F := MemLp.toLp_congr hT hF hTF
    rw [← hT_sum, hTeq] at hsum
    simpa only [hFn_sum] using hsum
  have hFn_actual (n : ℕ) (y : ℝ) :
      Fn n y = -deriv (fun t => a t * deriv (p n) t) y +
        j ^ 2 * c y * p n y + V y * p n y := by
    have hpd : ContDiff ℝ ∞ (deriv (p n)) := (contDiff_infty_iff_deriv.mp (hp n)).2
    have hprod : deriv (fun t => a t * deriv (p n) t) y =
        deriv a y * deriv (p n) y + a y * deriv (deriv (p n)) y :=
      ((ha.differentiable (by norm_num) y).hasDerivAt.fun_mul
        ((hpd.differentiable (by simp) y).hasDerivAt)).deriv
    rw [hprod]
    dsimp only [Fn, p₂, p₁, p₀, Pi.add_apply, Pi.mul_apply]
    ring
  have hG := n06_tendsto_unit_weighted_square hp₁ hv₁
    (cylinderWeight_continuous.pow 2) hlim₁
  have hL := n06_tendsto_unit_weighted_square hp₀ hv₀
    (cylinderWeight_continuous.pow 3) hlim₀
  have hD := n06_tendsto_unit_weighted_square hp₂ hv₂
    (cylinderWeight_continuous.pow 4) hlim₂
  have hB := n06_tendsto_unit_weighted_square hp₀ hv₀
    (cylinderWeight_continuous.pow 6) hlim₀
  have hJ := n06_tendsto_unit_weighted_square hp₁ hv₁
    (cylinderWeight_continuous.pow 5) hlim₁
  simp only [Pi.pow_apply] at hG hL hD hB hJ
  have hG' : Tendsto
      (fun n => ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (p n) y) ^ 2) atTop
      (𝓝 (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv v y) ^ 2)) := by
    simpa only [mul_pow] using hG
  have hD' : Tendsto
      (fun n => ∫ y in (0 : ℝ)..1,
        (cylinderWeight y ^ 2 * deriv (deriv (p n)) y) ^ 2) atTop
      (𝓝 (∫ y in (0 : ℝ)..1,
        (cylinderWeight y ^ 2 * deriv (deriv v) y) ^ 2)) := by
    simpa only [mul_pow, ← pow_mul] using hD
  have hleft := (((hG'.add (hL.const_mul (1 + j ^ 2))).add hD').add
    (hB.const_mul ((1 + j ^ 2) ^ 2))).add (hJ.const_mul (1 + j ^ 2))
  have hright := ((n06_tendsto_unit_square hFn hF hFlim).add
    (n06_tendsto_unit_square hp₀ hv₀ hlim₀)).const_mul (16384 * K ^ 10)
  exact le_of_tendsto_of_tendsto' hleft hright (fun n =>
    n06_smooth_cubic_graph_bound ha ((hp n).of_le (by simp)) hc hV hq
      (hFn_actual n) hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂)

/-- The exact N06 weak graph statement, starting only from L2 representatives and
their distributional modal equation. -/
theorem n06_weakGraphStatement : ContinuousFlexibility.Statements.N06WeakGraphStatement := by
  intro a c V q u F j K ha hc hV hq hu hF hweak hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have han (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : a y ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (div_pos zero_lt_one hKpos) (ha₁ y hy))
  obtain ⟨v, huv, hv, hvdAC, hv₀, hv₁, hv₂, hode, hodeExpanded⟩ :=
    n06_weak_mode_L2_regular zero_lt_one j ha han hc hV hu hF hweak
  refine ⟨v, huv, hv, hvdAC, hv₀, hv₁, hv₂, hode, ?_⟩
  have hbound := n06_regular_cubic_graph_bound (ha.of_le (by simp)) hv hvdAC hc hV hq
    hv₀ hv₁ hv₂ hF hodeExpanded hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  have hsq : (∫ y in (0 : ℝ)..1, v y ^ 2) = ∫ y in (0 : ℝ)..1, u y ^ 2 := by
    rw [n06_unit_intervalIntegral_eq, n06_unit_intervalIntegral_eq]
    apply integral_congr_ae
    filter_upwards [huv] with y hy
    rw [hy]
  rw [hsq] at hbound
  exact hbound

end ContinuousFlexibility.Analysis
