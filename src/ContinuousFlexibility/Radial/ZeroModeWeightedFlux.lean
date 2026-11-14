module

public import ContinuousFlexibility.Radial.ReferenceRadialKernelPairing
public import ContinuousFlexibility.Radial.ZeroModeWeightKernel
public import ContinuousFlexibility.Radial.ZeroModeWeakEquation

/-!
# Weighted estimates for the actual zero-mode flux

A kernel row is the constant inverse profile on one endpoint interval.
The existing pointwise inverse-profile estimate and the actual weighted
source pairing control it uniformly. Integrating the resulting flux
quotient gives the actual finite left height, without an extra regularity
assumption on the source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_endpointDistance_mono_left {a b s t : ℝ}
    (hs : s ≤ (a + b) / 2) (ht : t ≤ s) :
    min (t - a) (b - t) ≤ min (s - a) (b - s) := by
  have hmin : min (s - a) (b - s) = s - a :=
    min_eq_left (by linarith only [hs])
  rw [hmin]
  exact (min_le_left (t - a) (b - t)).trans (sub_le_sub_right ht a)

theorem zeroMode_endpointDistance_mono_right {a b s t : ℝ}
    (hs : (a + b) / 2 ≤ s) (ht : s ≤ t) :
    min (t - a) (b - t) ≤ min (s - a) (b - s) := by
  have hmin : min (s - a) (b - s) = b - s :=
    min_eq_right (by linarith only [hs])
  rw [hmin]
  exact (min_le_right (t - a) (b - t)).trans (sub_le_sub_left ht b)

theorem zeroMode_indicator_interval_integral
    {D : ReferenceData} {u v : ℝ} (huv : u ≤ v)
    (hI : Ioo u v ⊆ radialCore D) (c : ℝ) (f : ℝ → ℝ) :
    (∫ t in radialCore D, (Ioo u v).indicator (fun _ => c) t * f t) =
      c * ∫ t in u..v, f t := by
  calc
    _ = ∫ t in radialCore D, (Ioo u v).indicator (fun t => c * f t) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        by_cases ht : t ∈ Ioo u v <;> simp [Set.indicator, ht])
    _ = ∫ t in Ioo u v, c * f t := by
      rw [integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hI]
    _ = c * ∫ t in u..v, f t := by
      rw [integral_const_mul, intervalIntegral.integral_of_le huv,
        integral_Ioc_eq_integral_Ioo]

/-- The output cell is fixed while the flux point moves from that output
point toward the corresponding endpoint. -/
theorem zeroMode_weighted_sameSide_flux_bound
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ Mstar A : ℝ, 0 < Mstar ∧ 0 < A ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ f : ℝ → ℝ,
      MemLp f 2 (referenceRadialWeightedMeasure D γ M₀) →
      IntervalIntegrable f volume D.a D.b → (∫ t in D.a..D.b, f t) = 0 →
      ∀ k : ℕ, ∀ r s : ℝ, r ∈ D.cells k → s ∈ radialCore D →
      ((r ≤ (D.a + D.b) / 2 ∧ s ≤ r) ∨ ((D.a + D.b) / 2 ≤ r ∧ r ≤ s)) →
      (exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (zeroModeFlux D.a f s / D.w s)) ^ 2 ≤
      A * ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
  obtain ⟨Mstar, K, hMstar, hK, hpoint⟩ := zeroMode_weighted_inverseProfile_bound hD
  have hab : D.a < D.b := hD.1.2.1
  obtain ⟨B, hB, hpair⟩ := referenceRadial_kernel_pairing hab hD.2.1
  refine ⟨Mstar, (D.b - D.a) * (K ^ 2 * B), hMstar, by positivity, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ f hf hfi hmean k r s hr hs hside
  let c : ℝ :=
    exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) * (D.w s)⁻¹
  have hc : 0 ≤ c := mul_nonneg (exp_pos _).le (inv_pos.mpr (hD.1.2.2.2.2.1 s hs)).le
  have hinterval (u v : ℝ) (huv : u ≤ v) (hI : Ioo u v ⊆ radialCore D)
      (hdepth : ∀ t ∈ Ioo u v,
        min (t - D.a) (D.b - t) ≤ min (r - D.a) (D.b - r) ∧
        min (t - D.a) (D.b - t) ≤ min (s - D.a) (D.b - s)) :
      (c * ∫ t in u..v, f t) ^ 2 ≤
        ((D.b - D.a) * (K ^ 2 * B)) *
          ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
    let kernel : ℝ → ℝ := (Ioo u v).indicator (fun _ => c)
    have hk : Measurable kernel := measurable_const.indicator measurableSet_Ioo
    have hcell (m : ℕ) (t : ℝ) (ht : t ∈ D.cells m) :
        |kernel t| ≤ K *
          exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by
      by_cases hti : t ∈ Ioo u v
      · simp only [kernel, Set.indicator_of_mem hti, abs_of_nonneg hc]
        exact hpoint M₀ M₁ γ hM₀ hM₁ hγ k m r t s hr ht hs
          (hdepth t hti).1 (hdepth t hti).2
      · simp only [kernel, Set.indicator_of_notMem hti, abs_zero]
        exact mul_nonneg hK.le (exp_pos _).le
    have hp := (hpair γ M₀ K kernel f hK.le hk hf hcell).2.2
    simpa only [kernel, zeroMode_indicator_interval_integral huv hI] using hp
  rcases hside with ⟨hrmid, hsr⟩ | ⟨hrmid, hrs⟩
  · have hsmid : s ≤ (D.a + D.b) / 2 := hsr.trans hrmid
    have hi := hinterval D.a s hs.1.le
      (fun t ht => ⟨ht.1, ht.2.trans hs.2⟩) (by
        intro t ht
        have hts := zeroMode_endpointDistance_mono_left hsmid ht.2.le
        exact ⟨hts.trans (zeroMode_endpointDistance_mono_left hrmid hsr), hts⟩)
    calc
      (exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
          (zeroModeFlux D.a f s / D.w s)) ^ 2 =
          (c * ∫ t in D.a..s, f t) ^ 2 := by
        dsimp only [c, zeroModeFlux]
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := hi
  · have hsmid : (D.a + D.b) / 2 ≤ s := hrmid.trans hrs
    have hi := hinterval s D.b hs.2.le
      (fun t ht => ⟨hs.1.trans ht.1, ht.2⟩) (by
        intro t ht
        have hts := zeroMode_endpointDistance_mono_right hsmid ht.1.le
        exact ⟨hts.trans (zeroMode_endpointDistance_mono_right hrmid hrs), hts⟩)
    rw [zeroModeFlux_eq_neg_right_of_integrable hfi hmean ⟨hs.1.le, hs.2.le⟩]
    calc
      (exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
          (-(∫ t in s..D.b, f t) / D.w s)) ^ 2 =
          (c * ∫ t in s..D.b, f t) ^ 2 := by
        dsimp only [c]
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := hi

/-- Weighted source membership controls the actual flux quotient on the
whole core and proves its L1 integrability. The final estimate is for the
actual left endpoint value of the existing height primitive. -/
theorem zeroMode_quotient_integrable_of_weighted_source
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ Mstar A : ℝ, 0 < Mstar ∧ 0 < A ∧
      ∀ M₀ γ : ℝ, Mstar ≤ M₀ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ f : ℝ → ℝ,
      MemLp f 2 (referenceRadialWeightedMeasure D γ M₀) →
      IntervalIntegrable f volume D.a D.b → (∫ t in D.a..D.b, f t) = 0 →
      IntervalIntegrable (fun s => zeroModeFlux D.a f s / D.w s) volume D.a D.b ∧
      (∀ s ∈ radialCore D, (zeroModeFlux D.a f s / D.w s) ^ 2 ≤
        A * ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) ∧
      (zeroModeHeight D.a D.b D.w f D.a) ^ 2 ≤
        ((D.b - D.a) ^ 2 * A) *
          ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    change IsFiniteMeasure (volume.restrict (Ioo D.a D.b))
    infer_instance
  obtain ⟨Mstar, A, hMstar, hA, hflux⟩ := zeroMode_weighted_sameSide_flux_bound hD
  have hab : D.a < D.b := hD.1.2.1
  refine ⟨Mstar, A, hMstar, hA, ?_⟩
  intro M₀ γ hM₀ hγ f hf hfi hmean
  let E : ℝ := ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  let q : ℝ → ℝ := fun s => zeroModeFlux D.a f s / D.w s
  have hqbound (s : ℝ) (hs : s ∈ radialCore D) : (q s) ^ 2 ≤ A * E := by
    obtain ⟨k, hk⟩ := hD.2.1.exists_localizer_ne_zero hs
    have hsk : s ∈ D.cells k := hD.2.1.2.2.1 k hk
    have hside :
        (s ≤ (D.a + D.b) / 2 ∧ s ≤ s) ∨ ((D.a + D.b) / 2 ≤ s ∧ s ≤ s) := by
      rcases le_total s ((D.a + D.b) / 2) with h | h
      · exact Or.inl ⟨h, le_rfl⟩
      · exact Or.inr ⟨h, le_rfl⟩
    have hb := hflux M₀ 0 γ hM₀ le_rfl hγ f hf hfi hmean k s s hsk hs hside
    simp only [neg_zero, zero_mul, zero_add] at hb
    have hS : 0 ≤ radialS (D.cellIndex k) := by unfold radialS; positivity
    have hW : 1 ≤ exp (γ * radialS (D.cellIndex k)) :=
      one_le_exp_iff.mpr (mul_nonneg hγ.1 hS)
    have hWsq : 1 ≤ exp (γ * radialS (D.cellIndex k)) ^ 2 := by
      simpa only [one_pow] using (sq_le_sq₀ zero_le_one (exp_pos _).le).2 hW
    calc
      (q s) ^ 2 = 1 * (q s) ^ 2 := by ring
      _ ≤ exp (γ * radialS (D.cellIndex k)) ^ 2 * (q s) ^ 2 :=
        mul_le_mul_of_nonneg_right hWsq (sq_nonneg _)
      _ = (exp (γ * radialS (D.cellIndex k)) * q s) ^ 2 := by ring
      _ ≤ A * E := hb
  have hqcont : ContinuousOn q (radialCore D) :=
    zeroModeQuot_continuousOn_of_integrable hD.1.2.2.1.1.continuous.continuousOn
      (fun s hs => (hD.1.2.2.2.2.1 s hs).ne') hfi
  have hqm : MemLp q 2 (volume.restrict (radialCore D)) := by
    apply MemLp.of_bound (hqcont.aestronglyMeasurable measurableSet_Ioo) (sqrt (A * E))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs, sq_sqrt (mul_nonneg hA.le hE)]
    exact hqbound s hs
  have hqi : IntervalIntegrable q volume D.a D.b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr (hqm.integrable (by norm_num))
  refine ⟨hqi, hqbound, ?_⟩
  have henergy : (∫ s in radialCore D, q s ^ 2) ≤ (D.b - D.a) * (A * E) := by
    calc
      _ ≤ ∫ _ in radialCore D, A * E :=
        integral_mono_ae hqm.integrable_sq (integrable_const _)
          ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs => hqbound s hs))
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_def, Measure.restrict_apply_univ, radialCore,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul]
  calc
    (zeroModeHeight D.a D.b D.w f D.a) ^ 2 =
        (∫ s in radialCore D, q s) ^ 2 := by
      simp only [zeroModeHeight, neg_sq, intervalIntegral.integral_of_le hab.le,
        integral_Ioc_eq_integral_Ioo, radialCore, q]
    _ ≤ (D.b - D.a) * ∫ s in radialCore D, q s ^ 2 :=
      referenceRadial_integral_sq_le hab hqm
    _ ≤ (D.b - D.a) * ((D.b - D.a) * (A * E)) :=
      mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr hab.le)
    _ = _ := by ring

end ContinuousFlexibility.Radial
