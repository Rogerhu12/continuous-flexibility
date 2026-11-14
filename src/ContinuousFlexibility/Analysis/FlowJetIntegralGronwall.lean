module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowGronwall

/-!
# A uniform norm bound from the actual jet integral equation

Only the time integral of the coefficient multiplying the unknown jet
enters the exponential. The constant forcing bound remains a linear
prefactor. This applies to scalar jets and continuous multilinear maps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- The genuine vector-valued integral equation gives a uniform estimate
on the closed unit time interval, using only the integral angular bound. -/
theorem flowJet_norm_le_of_integral_equation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {u q : ℝ → V} {c : V} {α : ℝ → ℝ} {M Λ : ℝ}
    (hu : ContinuousOn u (Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hα0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t)
    (hM : 0 ≤ M) (hΛ : (∫ t in (0 : ℝ)..1, α t) ≤ Λ)
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, u t = c + ∫ r in (0 : ℝ)..t, q r)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ α t * ‖u t‖ + M) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ ≤ (‖c‖ + M) * Real.exp Λ := by
  intro t ht
  have hright : ContinuousOn (fun r => α r * ‖u r‖ + M) (Icc (0 : ℝ) 1) :=
    (hα.mul hu.norm).add continuousOn_const
  have hlin (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
      ‖u τ‖ ≤ ‖c‖ + ∫ r in (0 : ℝ)..τ, α r * ‖u r‖ + M := by
    have hτ1 : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hqI : IntervalIntegrable (fun r => ‖q r‖) volume 0 τ :=
      (hq.norm.mono (Icc_subset_Icc le_rfl hτ1.2)).intervalIntegrable_of_Icc hτ.1
    have hrI : IntervalIntegrable (fun r => α r * ‖u r‖ + M) volume 0 τ :=
      (hright.mono (Icc_subset_Icc le_rfl hτ1.2)).intervalIntegrable_of_Icc hτ.1
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hτ.1 hqI hrI
      (fun r hr => hbound r ⟨hr.1, hr.2.trans hτ1.2⟩)
    calc
      ‖u τ‖ = ‖c + ∫ r in (0 : ℝ)..τ, q r‖ := congrArg norm (heq τ hτ1)
      _ ≤ ‖c‖ + ‖∫ r in (0 : ℝ)..τ, q r‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ∫ r in (0 : ℝ)..τ, ‖q r‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hτ.1)
      _ ≤ _ := add_le_add le_rfl hmono
  have hg := integral_gronwall_of_continuousOn
    (u := fun r => ‖u r‖) (A := α) (B := fun _ => M) (δ := ‖c‖) ht.1
    (hu.norm.mono (Icc_subset_Icc le_rfl ht.2))
    (hα.mono (Icc_subset_Icc le_rfl ht.2)) continuousOn_const
    (fun r hr => hα0 r ⟨hr.1, hr.2.trans ht.2⟩) (fun _ _ => hM) hlin
  have hI0 : IntervalIntegrable α volume 0 t :=
    (hα.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hI1 : IntervalIntegrable α volume t 1 :=
    (hα.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  have hprefix : (∫ r in (0 : ℝ)..t, α r) ≤ Λ := by
    apply le_trans _ hΛ
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hI1]
    exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg ht.2
      (fun r hr => hα0 r ⟨ht.1.trans hr.1, hr.2⟩))
  have hfirst : ‖c‖ + (∫ _r in (0 : ℝ)..t, M) ≤ ‖c‖ + M := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    exact add_le_add le_rfl (mul_le_of_le_one_left hM ht.2)
  calc
    ‖u t‖ ≤ (‖c‖ + ∫ _r in (0 : ℝ)..t, M) *
        Real.exp (∫ r in (0 : ℝ)..t, α r) := hg
    _ ≤ (‖c‖ + M) * Real.exp (∫ r in (0 : ℝ)..t, α r) :=
      mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
    _ ≤ (‖c‖ + M) * Real.exp Λ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hprefix)
        (add_nonneg (norm_nonneg c) hM)

end ContinuousFlexibility.Analysis
