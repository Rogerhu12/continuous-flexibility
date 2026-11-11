import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Explicit cylinder norm bounds from radial support and actual jets

The cylinder measure of a radial strip is its radial length times pi.
Uniform bounds on a function supported in that strip therefore give its
actual L2 norm. The finite jet sum then gives the exact physical norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem materialCylinderMeasure_radial_strip {R : ℝ} (hR : 0 ≤ R) :
    materialCylinderMeasure (Icc (-R) R ×ˢ (univ : Set ℝ)) =
      ENNReal.ofReal (2 * R * Real.pi) := by
  rw [materialCylinderMeasure_eq_prod, Measure.prod_prod]
  simp only [angleMeasure, Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Ioc,
    sub_zero, sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (add_nonneg hR hR)]
  congr 1
  ring

theorem cylinder_eLpNorm_le_of_radial_support {f : PolarPoint → ℝ} {R K : ℝ}
    (hf : AEStronglyMeasurable f materialCylinderMeasure) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hzero : ∀ p : PolarPoint, R < |p.1| → f p = 0)
    (hbound : ∀ p : PolarPoint, |f p| ≤ K) :
    eLpNorm f 2 materialCylinderMeasure ≤
      ENNReal.ofReal (Real.sqrt (2 * R * Real.pi) * K) := by
  let U : Set PolarPoint := Icc (-R) R ×ˢ univ
  have hsupp : Function.support f ⊆ U := by
    intro p hp
    refine ⟨abs_le.mp ?_, mem_univ _⟩
    by_contra hnot
    exact hp (hzero p (lt_of_not_ge hnot))
  have hμ : materialCylinderMeasure U = ENNReal.ofReal (2 * R * Real.pi) :=
    materialCylinderMeasure_radial_strip hR
  have hV : 0 ≤ 2 * R * Real.pi :=
    mul_nonneg (mul_nonneg (by norm_num) hR) Real.pi_pos.le
  have hb := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (μ := materialCylinderMeasure.restrict U)
    hf.restrict (Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hbound p))
  rw [Measure.restrict_apply_univ, hμ] at hb
  have hexp : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hexp, ← ENNReal.ofReal_rpow_of_nonneg hV (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hb
  rw [eLpNorm_restrict_eq_of_support_subset hf hsupp] at hb
  exact hb

theorem cylinder_eLpNorm_toReal_le_of_radial_support {f : PolarPoint → ℝ} {R K : ℝ}
    (hf : AEStronglyMeasurable f materialCylinderMeasure) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hzero : ∀ p : PolarPoint, R < |p.1| → f p = 0)
    (hbound : ∀ p : PolarPoint, |f p| ≤ K) :
    (eLpNorm f 2 materialCylinderMeasure).toReal ≤ Real.sqrt (2 * R * Real.pi) * K := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (cylinder_eLpNorm_le_of_radial_support hf hR hK hzero hbound)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hK)] using h

theorem physicalNorm_le_of_common_jet_bound {T : MaterialData} {γ : ℝ}
    {f : PolarPoint → ℝ} {s : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ j : JetIndex s,
      eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
        2 materialCylinderMeasure ≤ ENNReal.ofReal L) :
    physicalNorm T γ s f ≤ Real.sqrt (Fintype.card (JetIndex s) : ℝ) * L := by
  classical
  have hsum : (∑ j : JetIndex s,
      eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
        2 materialCylinderMeasure ^ 2) ≤
      ENNReal.ofReal ((Fintype.card (JetIndex s) : ℝ) * L ^ 2) := by
    calc
      _ ≤ ∑ _j : JetIndex s, (ENNReal.ofReal L) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (zero_le _) (hb j) 2
      _ = (Fintype.card (JetIndex s) : ℝ≥0∞) * ENNReal.ofReal (L ^ 2) := by
        rw [← ENNReal.ofReal_pow hL]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg L))] at hreal
  unfold physicalNorm
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hL, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hreal

end ContinuousFlexibility.Statements
