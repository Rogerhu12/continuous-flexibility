import ContinuousFlexibility.Radial.ReferenceWeightedProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Cellwise comparison with the actual radial weighted measure

The partition identity and finite overlap convert any nonnegative
cellwise density bound into a measure comparison. The overlap constant
is chosen before the exponents and before the density, so the comparison
preserves uniformity of analytic estimates over an exponent interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real Filter MeasureTheory
open scoped ENNReal

theorem referenceRadial_withDensity_le_weighted
    {D : ReferenceData} (hpart : RadialPartition D) :
    ∃ B : ℝ, 0 < B ∧ ∀ γ M K : ℝ, ∀ g : ℝ → ℝ,
      0 ≤ K → (∀ r ∈ radialCore D, 0 ≤ g r) →
      (∀ m : ℕ, ∀ r ∈ D.cells m,
        g r ≤ K * exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))) →
      (volume.restrict (radialCore D)).withDensity (fun r => ENNReal.ofReal (g r)) ≤
        ENNReal.ofReal (K * B) • referenceRadialWeightedMeasure D γ M := by
  classical
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  let N : ℝ := (B : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨N, hN, ?_⟩
  intro γ M K g hK hg hcell
  have hpoint (r : ℝ) (hr : r ∈ radialCore D) :
      ENNReal.ofReal (g r) ≤ ENNReal.ofReal (K * N) *
        ∑' m : ℕ, referenceRadialCellDensity D γ M m r := by
    obtain ⟨hsfin, hcard⟩ := hB r
    let s : Finset ℕ := hsfin.toFinset
    have hsmem (m : ℕ) : m ∈ s ↔ D.localizer m r ≠ 0 := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hzero (m : ℕ) (hm : m ∉ s) : D.localizer m r = 0 := by
      by_contra hn
      exact hm ((hsmem m).mpr hn)
    have htsum : (∑' m : ℕ, D.localizer m r) = ∑ m ∈ s, D.localizer m r :=
      tsum_eq_sum hzero
    have hsum : (∑ m ∈ s, D.localizer m r) = 1 :=
      htsum.symm.trans (hpart.2.2.2.2.1 r hr).2
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
      exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        (D.localizer m r) ^ 2
    have hW0 (m : ℕ) : 0 ≤ W m := mul_nonneg (exp_pos _).le (sq_nonneg _)
    have hcells :
        g r * (∑ m ∈ s, (D.localizer m r) ^ 2) ≤ K * ∑ m ∈ s, W m := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hmr : r ∈ D.cells m := hpart.2.2.1 m ((hsmem m).mp hm)
      have hh := mul_le_mul_of_nonneg_right (hcell m r hmr)
        (sq_nonneg (D.localizer m r))
      simpa only [W, mul_assoc] using hh
    have hreal : g r ≤ (K * N) * ∑ m ∈ s, W m := by
      calc
        g r = g r * 1 := (mul_one _).symm
        _ ≤ g r * (N * ∑ m ∈ s, (D.localizer m r) ^ 2) :=
          mul_le_mul_of_nonneg_left hone (hg r hr)
        _ = N * (g r * ∑ m ∈ s, (D.localizer m r) ^ 2) := by ring
        _ ≤ N * (K * ∑ m ∈ s, W m) := mul_le_mul_of_nonneg_left hcells hN.le
        _ = (K * N) * ∑ m ∈ s, W m := by ring
    have henn := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (mul_nonneg hK hN.le),
      ENNReal.ofReal_sum_of_nonneg (fun m _ => hW0 m)] at henn
    change ENNReal.ofReal (g r) ≤
      ENNReal.ofReal (K * N) * ∑ m ∈ s, referenceRadialCellDensity D γ M m r at henn
    have hsumle :
        (∑ m ∈ s, referenceRadialCellDensity D γ M m r) ≤
          ∑' m : ℕ, referenceRadialCellDensity D γ M m r :=
      Summable.sum_le_tsum s (fun _ _ => bot_le) ENNReal.summable
    exact henn.trans (mul_le_mul le_rfl hsumle bot_le bot_le)
  let ρ : ℝ → ℝ≥0∞ := ∑' m : ℕ, referenceRadialCellDensity D γ M m
  have hρ (r : ℝ) : ρ r = ∑' m : ℕ, referenceRadialCellDensity D γ M m r :=
    Pi.tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable))
  have hdom :
      (volume.restrict (radialCore D)).withDensity (fun r => ENNReal.ofReal (g r)) ≤
      (volume.restrict (radialCore D)).withDensity (ENNReal.ofReal (K * N) • ρ) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    change ENNReal.ofReal (g r) ≤ ENNReal.ofReal (K * N) * ρ r
    rw [hρ]
    exact hpoint r hr
  calc
    (volume.restrict (radialCore D)).withDensity (fun r => ENNReal.ofReal (g r)) ≤
      (volume.restrict (radialCore D)).withDensity (ENNReal.ofReal (K * N) • ρ) := hdom
    _ = ENNReal.ofReal (K * N) • referenceRadialWeightedMeasure D γ M := by
      rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      dsimp only [ρ]
      rw [withDensity_tsum (referenceRadialCellDensity_measurable hpart γ M)]
      rfl

end ContinuousFlexibility.Statements
