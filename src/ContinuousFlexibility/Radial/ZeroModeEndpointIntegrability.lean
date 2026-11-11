import ContinuousFlexibility.Radial.ZeroModeEndpointWeight
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Endpoint L2 control from the frozen radial weighted measure

The finite overlap and the partition identity convert the cellwise
endpoint estimate into domination of the inverse-square-distance measure.
This proves ordinary L2 integrability of the endpoint quotient for every
member of the actual radial output space, including its measurability.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_endpoint_measure_le_weighted
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γlo : ℝ} (hγlo : 0 < γlo) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ : ℝ, γlo ≤ γ →
      (volume.restrict (radialCore D)).withDensity
        (fun r => ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2)) ≤
      ENNReal.ofReal K • referenceRadialWeightedMeasure D γ (-M) := by
  classical
  obtain ⟨K, hK, hcell⟩ := zeroMode_endpoint_inv_sq_le_outputWeight hD hγlo M
  have hpart := hD.2.1
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  let N : ℝ := (B : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨K * N, mul_pos hK hN, ?_⟩
  intro γ hγ
  have hpoint (r : ℝ) (hr : r ∈ radialCore D) :
      ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2) ≤
      ENNReal.ofReal (K * N) *
        ∑' m : ℕ, referenceRadialCellDensity D γ (-M) m r := by
    obtain ⟨hsfin, hcard⟩ := hB r
    let s : Finset ℕ := hsfin.toFinset
    have hsmem (m : ℕ) : m ∈ s ↔ D.localizer m r ≠ 0 := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hzero (m : ℕ) (hm : m ∉ s) : D.localizer m r = 0 := by
      by_contra hn
      exact hm ((hsmem m).mpr hn)
    have hsum : (∑ m ∈ s, D.localizer m r) = 1 := by
      rw [← tsum_eq_sum hzero]
      exact (hpart.2.2.2.2.1 r hr).2
    have hscard : s.card ≤ B := by
      simpa only [s, Set.ncard_eq_toFinset_card _ hsfin] using hcard
    have hCauchy :
        1 ≤ (s.card : ℝ) * ∑ m ∈ s, (D.localizer m r) ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum]
        using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1 : ℝ))
          (fun m => D.localizer m r)
    have hsum0 : 0 ≤ ∑ m ∈ s, (D.localizer m r) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg _)
    have hcardR : (s.card : ℝ) ≤ N := by
      have h : (s.card : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hscard
      dsimp [N]
      linarith
    have hone : 1 ≤ N * ∑ m ∈ s, (D.localizer m r) ^ 2 :=
      hCauchy.trans (mul_le_mul_of_nonneg_right hcardR hsum0)
    let W (m : ℕ) : ℝ :=
      exp (2 * (-M) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        (D.localizer m r) ^ 2
    have hW0 (m : ℕ) : 0 ≤ W m := mul_nonneg (exp_pos _).le (sq_nonneg _)
    have hcells :
        (min (r - D.a) (D.b - r))⁻¹ ^ 2 *
            (∑ m ∈ s, (D.localizer m r) ^ 2) ≤
          K * ∑ m ∈ s, W m := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hmr : r ∈ D.cells m := hpart.2.2.1 m ((hsmem m).mp hm)
      have hh := mul_le_mul_of_nonneg_right (hcell γ hγ m r hmr)
        (sq_nonneg (D.localizer m r))
      simpa only [W, mul_assoc] using hh
    have hreal :
        (min (r - D.a) (D.b - r))⁻¹ ^ 2 ≤ (K * N) * ∑ m ∈ s, W m := by
      calc
        (min (r - D.a) (D.b - r))⁻¹ ^ 2 =
            (min (r - D.a) (D.b - r))⁻¹ ^ 2 * 1 := (mul_one _).symm
        _ ≤ (min (r - D.a) (D.b - r))⁻¹ ^ 2 *
            (N * ∑ m ∈ s, (D.localizer m r) ^ 2) :=
          mul_le_mul_of_nonneg_left hone (sq_nonneg _)
        _ = N * ((min (r - D.a) (D.b - r))⁻¹ ^ 2 *
            ∑ m ∈ s, (D.localizer m r) ^ 2) := by ring
        _ ≤ N * (K * ∑ m ∈ s, W m) := mul_le_mul_of_nonneg_left hcells hN.le
        _ = (K * N) * ∑ m ∈ s, W m := by ring
    have henn := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (mul_pos hK hN).le,
      ENNReal.ofReal_sum_of_nonneg (fun m _ => hW0 m)] at henn
    change ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2) ≤
      ENNReal.ofReal (K * N) * ∑ m ∈ s, referenceRadialCellDensity D γ (-M) m r at henn
    exact henn.trans (mul_le_mul_left'
      (Summable.sum_le_tsum s (fun _ _ => bot_le) ENNReal.summable) _)
  let ρ : ℝ → ℝ≥0∞ := ∑' m : ℕ, referenceRadialCellDensity D γ (-M) m
  have hρ (r : ℝ) : ρ r = ∑' m : ℕ, referenceRadialCellDensity D γ (-M) m r :=
    Pi.tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable))
  have hdom :
      (volume.restrict (radialCore D)).withDensity
        (fun r => ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2)) ≤
      (volume.restrict (radialCore D)).withDensity (ENNReal.ofReal (K * N) • ρ) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    change ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2) ≤
      ENNReal.ofReal (K * N) * ρ r
    rw [hρ]
    exact hpoint r hr
  calc
    (volume.restrict (radialCore D)).withDensity
        (fun r => ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2)) ≤
      (volume.restrict (radialCore D)).withDensity (ENNReal.ofReal (K * N) • ρ) := hdom
    _ = ENNReal.ofReal (K * N) • referenceRadialWeightedMeasure D γ (-M) := by
      rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      dsimp only [ρ]
      rw [withDensity_tsum (referenceRadialCellDensity_measurable hpart γ (-M))]
      rfl

/-- Membership in the actual radial output measure gives ordinary L2
control after division by the endpoint distance. -/
theorem zeroMode_memLp_div_endpointDistance
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γ M : ℝ} (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (referenceRadialWeightedMeasure D γ (-M))) :
    MemLp (fun r => u r / min (r - D.a) (D.b - r)) 2
      (volume.restrict (radialCore D)) := by
  obtain ⟨K, _, hK⟩ := zeroMode_endpoint_measure_le_weighted hD hγ M
  let d (r : ℝ) : ℝ := min (r - D.a) (D.b - r)
  let σ (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((d r)⁻¹ ^ 2)
  have hd : Measurable d :=
    (measurable_id.sub measurable_const).min (measurable_const.sub measurable_id)
  have hσ : Measurable σ := (hd.inv.pow_const 2).ennreal_ofReal
  have hum : MemLp u 2 ((volume.restrict (radialCore D)).withDensity σ) :=
    hu.of_measure_le_smul ENNReal.ofReal_ne_top (hK γ le_rfl)
  have hσne : ∀ᵐ r ∂volume.restrict (radialCore D), σ r ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply sq_pos_of_pos
    apply inv_pos.mpr
    exact lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hua : AEStronglyMeasurable u (volume.restrict (radialCore D)) :=
    hum.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous' hσ.aemeasurable hσne)
  have hquot : AEStronglyMeasurable (fun r => u r / d r)
      (volume.restrict (radialCore D)) :=
    hua.div hd.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hquot).mpr
  have hisq := (integrable_withDensity_iff_integrable_smul' hσ
    (ae_of_all _ (fun r => ENNReal.ofReal_ne_top))).mp hum.integrable_sq
  convert hisq using 1
  funext r
  simp only [σ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Radial
