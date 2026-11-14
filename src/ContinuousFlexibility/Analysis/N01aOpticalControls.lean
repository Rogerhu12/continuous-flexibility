module

public import ContinuousFlexibility.Analysis.N01aOpticalWeights

/-!
# Uniform optical controls from actual profile bounds

The input estimates concern the actual radicand and actual optical travel
on each negative component. The output is a family of globally smooth,
compactly supported logarithmic controls whose actual travel derivative
is one, with one coefficient power for every derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Quantitative controls on an arbitrary family of negative components.
No bound for a derivative at a turning point is required. -/
theorem exists_n01a_uniform_opticalControls {ι : Type*}
    {w : ℝ → ℝ} {l h E : ι → ℝ} {α β A : ℝ}
    (hα : 0 < α) (hαβ : α < β) (hA : 0 < A)
    (hgeom : ∀ i, α ≤ l i ∧ l i < h i ∧ h i ≤ β)
    (hE : ∀ i, 1 ≤ E i) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ i r, r ∈ Icc (l i) (h i) → 0 < w r)
    (hneg : ∀ i r, r ∈ Ioo (l i) (h i) → deriv w r < 0)
    (hroots : ∀ i, deriv w (l i) = 0 ∧ deriv w (h i) = 0)
    (htravel : ∀ i, E i ^ (-A) ≤ opticalTravel w (l i) (h i))
    (hjets : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i r, r ∈ Icc (l i) (h i) →
      |iteratedDeriv s (n01aOpticalRadicand w) r| ≤ C * E i ^ C) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ Ioo (l i) (h i)) ∧
      (∀ i, HasDerivAt
        (fun t : ℝ => ∫ r in l i..h i,
          Real.sqrt (-deriv (fun x => w x * Real.exp (t * χ i x)) r /
            (r * (w r * Real.exp (t * χ i r))))) 1 0) ∧
      (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i r,
        |iteratedDeriv s (χ i) r| ≤ B * E i ^ B) := by
  let L : ℝ := β - α
  have hL : 0 < L := sub_pos.mpr hαβ
  have hβ : 0 < β := hα.trans hαβ
  have hl (i : ι) : 0 < l i := hα.trans_le (hgeom i).1
  have hEpos (i : ι) : 0 < E i := zero_lt_one.trans_le (hE i)
  let δ : ι → ℝ := fun i => n01aOpticalScale (E i) A L
  have hδ (i : ι) : 0 < δ i := n01aOpticalScale_pos (hEpos i) hL
  obtain ⟨D, hD, hDmajor⟩ := n01aOptical_absorb_power ((4 * L) ^ 2) (2 * A) (sq_nonneg _)
  have hδinv (i : ι) : (δ i)⁻¹ ≤ D * E i ^ D := by
    dsimp only [δ]
    rw [n01aOpticalScale_inv (hEpos i)]
    exact hDmajor (E i) (hE i)
  obtain ⟨K, hK, hKjets⟩ := n01aOptical_finite_weightedJet_bound hE hjets 1
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let k : ι → ℝ := fun i => K * E i ^ K
  have hk (i : ι) : 1 ≤ k i := by
    calc
      1 ≤ K := hK
      _ ≤ K * E i ^ K := le_mul_of_one_le_right hKpos.le
        (Real.one_le_rpow (hE i) hKpos.le)
  have hkernel (i : ι) :
      0 < (∫ r in l i..h i, n01aOpticalKernel w (δ i) r) ∧
        |n01aOpticalNormalizer w (l i) (h i) (δ i)| ≤ β * (k i) ^ 2 / δ i := by
    have hq : ContinuousOn (n01aOpticalRadicand w) (Icc (l i) (h i)) :=
      fun r hr => (contDiffAt_n01aOpticalRadicand hw
        ((hl i).trans_le hr.1).ne' (hpos i r hr).ne').continuousAt.continuousWithinAt
    have hwidth : h i - l i ≤ L := by
      dsimp only [L]
      linarith [(hgeom i).1, (hgeom i).2.2]
    have hmargin : 4 * L * Real.sqrt (δ i) ≤
        ∫ r in l i..h i, Real.sqrt (n01aOpticalRadicand w r) := by
      rw [show 4 * L * Real.sqrt (δ i) = E i ^ (-A) from
        n01aOpticalScale_sqrt (hEpos i) hL]
      exact htravel i
    obtain ⟨p, hp, hpeak⟩ := exists_n01aOpticalPeak (hgeom i).2.1 hL hwidth (hδ i) hq hmargin
    have hfirst (r : ℝ) (hr : r ∈ Icc (l i) (h i)) :
        |deriv (n01aOpticalRadicand w) r| ≤ k i := by
      simpa only [iteratedDeriv_one] using hKjets 1 le_rfl i r hr
    have hzero (r : ℝ) (hr : r ∈ Icc (l i) (h i)) :
        n01aOpticalRadicand w r ≤ (k i) ^ 2 := by
      have hqbound : |n01aOpticalRadicand w r| ≤ k i := by
        simpa only [iteratedDeriv_zero] using hKjets 0 (by omega) i r hr
      exact (le_abs_self _).trans (hqbound.trans (le_self_pow₀ (hk i) (by norm_num)))
    exact n01aOpticalNormalizer_bound (hl i) (hδ i) (zero_lt_one.trans_le (hk i))
      (hgeom i).2.2 hw (hpos i) (hroots i).1 (hroots i).2 hfirst hzero hp hpeak
  obtain ⟨N, hN, hNmajor⟩ := n01aOptical_quadratic_scale_bound hβ.le hKpos hD
  have hnormalizer (i : ι) :
      |n01aOpticalNormalizer w (l i) (h i) (δ i)| ≤ N * E i ^ N :=
    (hkernel i).2.trans (hNmajor (E i) (δ i) (hE i) (hδ i) (hδinv i))
  let χ : ι → ℝ → ℝ := fun i => n01aOpticalControl w (l i) (h i) (δ i)
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro i
    exact ⟨contDiff_n01aOpticalControl (hl i) (hδ i) hw (hpos i) (hroots i).1 (hroots i).2,
      hasCompactSupport_n01aOpticalControl (hl i) (hδ i) hw (hpos i) (hroots i).1 (hroots i).2,
      tsupport_n01aOpticalControl_subset (hl i) (hδ i) hw (hpos i) (hroots i).1 (hroots i).2⟩
  · intro i
    have hd := hasDerivAt_n01aOpticalControl_travel (hl i) (hgeom i).2.1 (hδ i)
      hw (hpos i) (hneg i) (hroots i).1 (hroots i).2 (hkernel i).1
    have hpert (t : ℝ) : opticalLogPerturbation w (n01aOpticalControl w (l i) (h i) (δ i)) t =
        (fun x => w x * Real.exp (t * χ i x)) := rfl
    simpa only [opticalTravel, opticalSpeed, hpert] using hd
  · intro s
    obtain ⟨Aₛ, hAₛ, hfinite⟩ := n01aOptical_finite_weightedJet_bound hE hjets s
    have hAₛpos : 0 < Aₛ := zero_lt_one.trans_le hAₛ
    obtain ⟨F, hF, hraw⟩ := n01aOpticalRawControl_finiteJet_bound s
    obtain ⟨R, hR, hRmajor⟩ := n01aOptical_polynomial_scale_bound s hF hβ.le hAₛpos hD
    obtain ⟨B, hB, hBmajor⟩ := n01aOptical_power_product_bound hN hR
    refine ⟨B, hB, fun i r => ?_⟩
    have hrawbound : |iteratedDeriv s (n01aOpticalRawControl w (l i) (h i) (δ i)) r| ≤
        R * E i ^ R := by
      have hraw' := hraw (K := Aₛ * E i ^ Aₛ) (β := β) (hl i) (hδ i)
        (mul_nonneg hAₛpos.le (Real.rpow_nonneg (hEpos i).le _)) hβ.le
        (hgeom i).2.2 hw (hpos i) (hroots i).1 (hroots i).2
        (fun j hj x hx => hfinite j hj i x hx) r
      exact hraw'.trans (hRmajor (E i) (δ i) (hE i) (hδ i) (hδinv i))
    change |iteratedDeriv s (n01aOpticalControl w (l i) (h i) (δ i)) r| ≤ B * E i ^ B
    rw [iteratedDeriv_n01aOpticalControl, abs_mul]
    exact (mul_le_mul (hnormalizer i) hrawbound (abs_nonneg _)
      (mul_nonneg hN.le (Real.rpow_nonneg (hEpos i).le _))).trans (hBmajor (E i) (hE i))

end ContinuousFlexibility.Statements
