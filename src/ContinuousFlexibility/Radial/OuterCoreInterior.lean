module

public import ContinuousFlexibility.Radial.OuterCellInterior
public import ContinuousFlexibility.Radial.OuterCoreTransfer

/-!
# Pointwise energy throughout the ordinary transition core

The same estimate applies between any two physical points of the core.
This supplies the homogeneous kernel bounds needed inside the core,
as well as the endpoint transfer estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def outerCoreInteriorQuadraticExponent (C : ℕ → ℝ) (K a Cstar L : ℝ) : ℝ :=
  outerCoreQuadraticExponent C K a Cstar L + outerFrequencyExponent Cstar + 10

theorem outer_positive_physical_energy_on {D : ReferenceData} {j scale l r s t : ℝ} {u z : ℝ → ℝ}
    (hD : RadialProfileGeometry D) (hscale : 0 < scale) (hlr : l < r)
    (hsub : Icc l r ⊆ radialCore D)
    (hslope : ∀ x ∈ Ioo l r, 2 / x ≤ deriv D.w x / D.w x)
    (hstate : ∀ x ∈ Icc l r, HasDerivAt u (scale / D.w x * z x) x ∧
      HasDerivAt z (j ^ 2 * deriv D.w x / (scale * x) * u x) x)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) * outerPositivePhysicalFactor D j scale l r := by
  have hw := hD.2.2.1.1
  have hdc : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x := hD.2.2.2.2.1 x (hsub hx)
  have hxp (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  have hmono := morseConnector_monotone_of_logSlope hw
    (hxp l (left_mem_Icc.mpr hlr.le)) hwp hslope
  have hderiv₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ deriv D.w x := by
    have hh := hmono.derivWithin_nonneg (x := x)
    rwa [((hw.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hlr x hx)] at hh
  have hα : ContinuousOn (fun x => scale / D.w x) (Icc l r) :=
    continuousOn_const.div hw.continuous.continuousOn (fun x hx => (hwp x hx).ne')
  have hβ : ContinuousOn (fun x => j ^ 2 * deriv D.w x / (scale * x)) (Icc l r) :=
    (continuousOn_const.mul hdc.continuousOn).div (continuousOn_const.mul continuousOn_id)
      (fun x hx => (mul_pos hscale (hxp x hx)).ne')
  exact transfer_positive_piece_regularized_on hlr.le hα hβ
    (fun x hx => div_nonneg hscale.le (hwp x hx).le)
    (fun x hx => div_nonneg (mul_nonneg (sq_nonneg j) (hderiv₀ x hx))
      (mul_nonneg hscale.le (hxp x hx).le)) hstate hs ht

theorem morseRealized_cell_energy_on_exp_of_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (hL : 0 ≤ L) (side : Bool) (hn : T.index ≤ n) (hn1 : 1 ≤ n)
    (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)))
    (ht : t ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n))) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp ((4 * L + 11 * outerFrequencyExponent Cstar + 500010) * (n : ℝ) ^ 2 +
        10 * ((j : ℝ) * sqrt (morseChainA T n))) := by
  have hM : 1 ≤ exp (L * (n : ℝ) ^ 2) :=
    one_le_exp_iff.mpr (mul_nonneg hL (sq_nonneg _))
  have he := morseRealized_cell_energy_on h hσ hscale hM side n hn hhi hlo hstate hs ht
  have hc := morse_cell_factor_le_frequency_exp_of_upper hn1 (h.d_eq n hn) hupper
  have hp := outer_morse_peak_factor_le_of_upper hn1 (h.d_eq n hn) hupper
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ exp (L * (n : ℝ) ^ 2) ^ 4 *
        (exp ((outerFrequencyExponent Cstar + 10) * (n : ℝ) ^ 2) *
          exp ((10 * outerFrequencyExponent Cstar + 500000) * (n : ℝ) ^ 2 +
            10 * ((j : ℝ) * sqrt (morseChainA T n)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hp hc (morseCellEnergyFactor_nonneg _ _ _ _) (exp_pos _).le)
        (by positivity)
    _ = _ := by
      rw [outer_exp_pow_four, ← exp_add, ← exp_add]
      congr 1
      ring

theorem morseOuterCore_energy_on_exp_of_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n))
    (ht : t ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (outerCoreInteriorQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  let N := (n : ℝ) ^ 2
  let F := outerFrequencyExponent Cstar
  let tau := (j : ℝ) * sqrt (morseChainA T n)
  let E (x : ℝ) := u x ^ 2 + z x ^ 2
  let Fc := exp ((4 * L + 11 * F + 500010) * N + 10 * tau)
  let Fj := exp ((4 * (outerJoinPrefactor C K D.a + (F + L + 32)) + 2) * N +
    2 * sqrt (outerJoinActionCoefficient C K D.a) * tau)
  have hn1 : 1 ≤ n := by omega
  have hk : T.index ≤ n - 1 := by omega
  have hpred : n - 1 + 1 = n := by omega
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hFc : 1 ≤ Fc := one_le_exp_iff.mpr
    (by dsimp only [Fc, F, N, tau, outerFrequencyExponent]; positivity)
  have hFj : 1 ≤ Fj := one_le_exp_iff.mpr
    (by dsimp only [Fj, F, N, tau, outerFrequencyExponent, outerJoinPrefactor]; positivity)
  have hprod : Fc * Fj =
      exp (outerCoreInteriorQuadraticExponent C K D.a Cstar L * N +
        outerCoreActionExponent C K D.a * tau) := by
    dsimp only [Fc, Fj]
    rw [← exp_add]
    congr 1
    dsimp only [outerCoreInteriorQuadraticExponent, outerCoreQuadraticExponent, outerCoreActionExponent, F]
    ring
  have hpieces := morseOuterCore_contains_pieces h side n hn
  have hcore := morseOuterCore_interval h side n hn
  have hcend := morseRealized_retained_endpoints h side n hn.le
  have hj := h.join_data side (n - 1) hk
  have hce : ∀ s ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)),
      ∀ t ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)),
      E t ≤ E s * Fc :=
    fun s hs t ht => morseRealized_cell_energy_on_exp_of_upper h hσ hscale hL side hn.le hn1
      hupper hhi hlo (fun r hr => hstate r (hpieces.1 hr)) hs ht
  have hjf := morse_preceding_join_factor_le_frequency_exp_of_upper h hσ hcell hscale hL side hn hupper hhi hlo
  have hje : ∀ s ∈ Icc (T.joinLeft side (n - 1)) (T.joinRight side (n - 1)),
      ∀ t ∈ Icc (T.joinLeft side (n - 1)) (T.joinRight side (n - 1)),
      E t ≤ E s * Fj := by
    intro s hs t ht
    exact (outer_positive_physical_energy_on h.geometry hscale hj.1
      (hpieces.2.trans hcore.2) hj.2.2.2.2 (fun r hr => hstate r (hpieces.2 hr)) hs ht).trans
        (mul_le_mul_of_nonneg_left hjf (by positivity))
  cases side with
  | false =>
      have hseam : T.joinLeft false (n - 1) = T.radius false n (T.rightX false n) := by
        simpa only [Bool.false_eq_true, ite_false, hpred] using hj.2.1
      rw [hseam] at hje
      have hbc : T.radius false n (T.rightX false n) ≤ T.joinRight false (n - 1) := by
        rw [← hseam]
        exact hj.1.le
      have hh := energy_transfer_join hcend.2.2.le hbc hFc hFj
        (fun x _ => show 0 ≤ E x by dsimp only [E]; positivity) hce hje hs ht
      rw [hprod] at hh
      exact hh
  | true =>
      have hseam : T.joinRight true (n - 1) = T.radius true n (T.leftX true n) := by
        simpa only [ite_true, hpred] using hj.2.2.1
      rw [hseam] at hje
      have hab : T.joinLeft true (n - 1) ≤ T.radius true n (T.leftX true n) := by
        rw [← hseam]
        exact hj.1.le
      have hh := energy_transfer_join hab hcend.2.2.le hFj hFc
        (fun x _ => show 0 ≤ E x by dsimp only [E]; positivity) hje hce hs ht
      rw [mul_comm Fj Fc, hprod] at hh
      exact hh

theorem morseRealized_cell_energy_on_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (hL : 0 ≤ L) (side : Bool) (hn : T.index ≤ n) (hn1 : 1 ≤ n)
    (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)))
    (ht : t ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n))) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp ((4 * L + 11 * outerFrequencyExponent Cstar + 500010) * (n : ℝ) ^ 2 +
        10 * ((j : ℝ) * sqrt (morseChainA T n))) :=
  morseRealized_cell_energy_on_exp_of_upper h hσ hscale hL side hn hn1 hband.2.2 hhi hlo hstate hs ht

theorem morseOuterCore_energy_on_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n))
    (ht : t ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (outerCoreInteriorQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) :=
  morseOuterCore_energy_on_exp_of_upper h hσ hcell hscale hL side hn hband.2.2 hhi hlo hstate hs ht

end ContinuousFlexibility.Radial
