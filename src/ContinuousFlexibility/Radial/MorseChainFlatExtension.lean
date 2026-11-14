module

public import ContinuousFlexibility.Radial.MorseChainLocalGluing
public import ContinuousFlexibility.Radial.MorseChainEndpointDistances
public import ContinuousFlexibility.Analysis.FlatExtension

/-!
# Flatness at the actual outward accumulation radius

The exponential derivative bounds are compared to the square of the
actual distance to the endpoint. The existing one-sided extension
theorem is then applied by reflection to this same glued function.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

/-- The existing actual one-sided extension applies to an outward
coordinate by reflecting it, including equality of the original function
with the reflected extension and vanishing of all exterior derivatives. -/
theorem contDiff_flat_of_left_jet_limits {w : ℝ → ℝ} {endpoint : ℝ}
    (hW : ContDiffOn ℝ ∞ w (Iio endpoint))
    (hZero : ∀ x, endpoint ≤ x → w x = 0)
    (hLim : ∀ k, Tendsto (iteratedDeriv k w) (𝓝[<] endpoint) (𝓝 0)) :
    ContDiff ℝ ∞ w ∧ ∀ k x, endpoint ≤ x → iteratedDeriv k w x = 0 := by
  let f : ℝ → ℝ := fun y => w (-y)
  have hneg : MapsTo (fun y : ℝ => -y) (Ioi (-endpoint)) (Iio endpoint) := by
    intro y hy
    change -y < endpoint
    simpa only [neg_neg] using neg_lt_neg (mem_Ioi.mp hy)
  have hf : ContDiffOn ℝ ∞ f (Ioi (-endpoint)) :=
    hW.comp contDiff_id.neg.contDiffOn hneg
  have hnegT : Tendsto (fun y : ℝ => -y) (𝓝[>] (-endpoint)) (𝓝[<] endpoint) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [neg_neg] using
        ((continuous_neg : Continuous (fun y : ℝ => -y)).continuousAt (x := -endpoint)).tendsto.mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hneg hy
  have hfLim (k : ℕ) : Tendsto (iteratedDeriv k f) (𝓝[>] (-endpoint)) (𝓝 0) := by
    have hEq : iteratedDeriv k f = fun y => ((-1 : ℝ) ^ k) • iteratedDeriv k w (-y) :=
      funext (iteratedDeriv_comp_neg k w)
    rw [hEq]
    simpa only [Function.comp_apply, smul_zero] using
      (tendsto_const_nhds (x := ((-1 : ℝ) ^ k))).smul ((hLim k).comp hnegT)
  let W := Analysis.extendZeroLeft (-endpoint) f
  have hWs : ContDiff ℝ ∞ W := Analysis.contDiff_extendZeroLeft hf hfLim
  have he : w = fun x => W (-x) := by
    funext x
    by_cases hx : x < endpoint
    · simpa only [f, neg_neg] using (Analysis.extendZeroLeft_of_gt (f := f) (neg_lt_neg hx)).symm
    · rw [hZero x (le_of_not_gt hx)]
      exact (Analysis.extendZeroLeft_of_le (f := f) (neg_le_neg (le_of_not_gt hx))).symm
  rw [he]
  refine ⟨hWs.comp contDiff_id.neg, ?_⟩
  intro k x hx
  rw [iteratedDeriv_comp_neg]
  change ((-1 : ℝ) ^ k) • iteratedDeriv k (Analysis.extendZeroLeft (-endpoint) f) (-x) = 0
  rw [Analysis.iteratedDeriv_extendZeroLeft_eq_zero hf hfLim (neg_le_neg hx) k, smul_zero]

/-- A quadratic decay bound on each actual ordinary derivative implies
all one-sided derivative limits needed for the flat extension. -/
theorem contDiff_flat_of_quadratic_jets {w : ℝ → ℝ} {endpoint : ℝ}
    (hW : ContDiffOn ℝ ∞ w (Iio endpoint))
    (hZero : ∀ x, endpoint ≤ x → w x = 0)
    (hBound : ∀ k, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x ∈ Ioo (endpoint - δ) endpoint,
      |iteratedDeriv k w x| ≤ C * (endpoint - x) ^ 2) :
    ContDiff ℝ ∞ w ∧ ∀ k x, endpoint ≤ x → iteratedDeriv k w x = 0 := by
  apply contDiff_flat_of_left_jet_limits hW hZero
  intro k
  obtain ⟨δ, C, hδ, _, hB⟩ := hBound k
  have hNear : ∀ᶠ x in 𝓝[<] endpoint, x ∈ Ioi (endpoint - δ) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (show endpoint - δ < endpoint by linarith only [hδ]))
  apply squeeze_zero_norm'
  · filter_upwards [hNear, self_mem_nhdsWithin] with x hx₁ hx₂
    simpa only [Real.norm_eq_abs] using hB x ⟨hx₁, hx₂⟩
  · have hC : Continuous (fun x : ℝ => C * (endpoint - x) ^ 2) :=
      continuous_const.mul ((continuous_const.sub continuous_id).pow 2)
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      (hC.continuousAt (x := endpoint)).tendsto.mono_left nhdsWithin_le_nhds

private theorem morse_exp_decay_eventual_square (C : ℝ) (N : ℕ) :
    ∃ M : ℕ, ∀ n, M ≤ n →
      exp (-((N + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) + C * ((N + n : ℕ) : ℝ) ^ 2) ≤
        exp (-(((N + n : ℕ) : ℝ) + 1) ^ 2) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max 1 ((C + 8) ^ 2))
  refine ⟨M, ?_⟩
  intro n hn
  let t : ℝ := (N + n : ℕ)
  have hMt : (M : ℝ) ≤ t := by
    change (M : ℝ) ≤ ((N + n : ℕ) : ℝ)
    exact_mod_cast (show M ≤ N + n by omega)
  have ht : 1 ≤ t := (le_max_left _ _).trans (hM.trans hMt)
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hC : C + 8 ≤ sqrt t := calc
    _ ≤ |C + 8| := le_abs_self _
    _ = sqrt ((C + 8) ^ 2) := (sqrt_sq_eq_abs _).symm
    _ ≤ _ := sqrt_le_sqrt ((le_max_right _ _).trans (hM.trans hMt))
  have hpow : t ^ (5 / 2 : ℝ) = t ^ 2 * sqrt t := calc
    _ = t ^ ((2 : ℝ) + 1 / 2) := by congr 1; norm_num
    _ = t ^ (2 : ℝ) * t ^ (1 / (2 : ℝ)) := rpow_add htp _ _
    _ = _ := by rw [← sqrt_eq_rpow, show t ^ (2 : ℝ) = t ^ (2 : ℕ) from rpow_natCast t 2]
  have ht₂ : (t + 1) ^ 2 ≤ (2 * t) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [ht]) 2
  change exp (-t ^ (5 / 2 : ℝ) + C * t ^ 2) ≤ exp (-(t + 1) ^ 2) ^ 2
  rw [hpow, ← exp_nat_mul]
  apply exp_le_exp.mpr
  calc
    -(t ^ 2 * sqrt t) + C * t ^ 2 = (C - sqrt t) * t ^ 2 := by ring
    _ ≤ (-8 : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hC]) (sq_nonneg t)
    _ = (-2 : ℝ) * (2 * t) ^ 2 := by ring
    _ ≤ (-2 : ℝ) * (t + 1) ^ 2 := mul_le_mul_of_nonpos_left ht₂ (by norm_num)
    _ = ((2 : ℕ) : ℝ) * -(t + 1) ^ 2 := by
      norm_num only [Nat.cast_ofNat, mul_neg, neg_mul]

/-- The actual exponential bounds and actual outward endpoint distances
imply quadratic decay of every ordinary derivative of the same function. -/
theorem morse_quadratic_jets_of_exp_bounds {w : ℝ → ℝ} {enter : ℕ → ℝ}
    {endpoint d : ℝ} (N : ℕ) (hd : 0 < d)
    (hmono : StrictMono enter) (hLim : Tendsto enter atTop (𝓝 endpoint))
    (hDist : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      d * exp (-(((N + n : ℕ) : ℝ) + 1) ^ 2) ≤ endpoint - x)
    (hExp : ∀ k, ∃ C B : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      |iteratedDeriv k w x| ≤ C *
        exp (-((N + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) + B * ((N + n : ℕ) : ℝ) ^ 2)) :
    ∀ k, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x ∈ Ioo (endpoint - δ) endpoint,
      |iteratedDeriv k w x| ≤ C * (endpoint - x) ^ 2 := by
  intro k
  obtain ⟨C, B, hC, hExpB⟩ := hExp k
  obtain ⟨M, hM⟩ := morse_exp_decay_eventual_square B N
  have hbound (n : ℕ) : enter n ≤ endpoint := by
    apply ge_of_tendsto hLim
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hmono.monotone hm
  have hMlt : enter M < endpoint := (hmono (Nat.lt_succ_self M)).trans_le (hbound (M + 1))
  refine ⟨endpoint - enter M, C / d ^ 2, sub_pos.mpr hMlt, div_nonneg hC (sq_nonneg d), ?_⟩
  intro x hx
  have hxM : enter M < x := by linarith only [hx.1]
  obtain ⟨n, hn⟩ := morse_outward_block_exists hLim
    ((hmono.monotone (Nat.zero_le M)).trans hxM.le) hx.2
  have hMn : M ≤ n := by
    by_contra h
    have he : n + 1 ≤ M := by omega
    exact (not_lt_of_ge ((hmono.monotone he).trans hxM.le)) hn.2
  have hx' : x ∈ Icc (enter n) (enter (n + 1)) := ⟨hn.1, hn.2.le⟩
  let E := exp (-(((N + n : ℕ) : ℝ) + 1) ^ 2)
  have hE : 0 < E := exp_pos _
  have hEratio : E ≤ (endpoint - x) / d := by
    apply (le_div_iff₀ hd).mpr
    rw [mul_comm E d]
    exact hDist n x hx'
  calc
    _ ≤ C * exp (-((N + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) + B * ((N + n : ℕ) : ℝ) ^ 2) := hExpB n x hx'
    _ ≤ C * E ^ 2 := mul_le_mul_of_nonneg_left (hM n hMn) hC
    _ ≤ C * ((endpoint - x) / d) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE.le hEratio 2) hC
    _ = _ := by rw [div_pow]; ring

/-- The actual piecewise choice of smooth pieces is flat at the actual
accumulation radius once its individual physical jets satisfy the
uniform exponential bounds. -/
theorem contDiff_flat_morseOutwardGlue {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    {endpoint d : ℝ} (N : ℕ) (hd : 0 < d)
    (hmono : StrictMono enter) (hLim : Tendsto enter atTop (𝓝 endpoint))
    (hpiece : ∀ n, ContDiff ℝ ∞ (piece n))
    (hmatch : ∀ n, piece n =ᶠ[𝓝 (enter (n + 1))] piece (n + 1))
    (hDist : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      d * exp (-(((N + n : ℕ) : ℝ) + 1) ^ 2) ≤ endpoint - x)
    (hExp : ∀ k, ∃ C B : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      |iteratedDeriv k (piece n) x| ≤ C *
        exp (-((N + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) + B * ((N + n : ℕ) : ℝ) ^ 2)) :
    ContDiff ℝ ∞ (morseOutwardGlue enter piece) ∧
      ∀ k x, endpoint ≤ x → iteratedDeriv k (morseOutwardGlue enter piece) x = 0 := by
  apply contDiff_flat_of_quadratic_jets (contDiffOn_morseOutwardGlue hmono hLim hpiece hmatch)
    (fun x hx => morseOutwardGlue_eq_zero_of_le hmono hLim hx)
  apply morse_quadratic_jets_of_exp_bounds N hd hmono hLim hDist
  intro k
  obtain ⟨C, B, hC, h⟩ := hExp k
  refine ⟨C, B, hC, ?_⟩
  intro n x hx
  rw [morseOutwardGlue_iteratedDeriv_eq hmono hmatch hx]
  exact h n x hx

end ContinuousFlexibility.Radial
