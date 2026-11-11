import ContinuousFlexibility.Analysis.N07aMaterialPullbackJets
import ContinuousFlexibility.Analysis.N07aMaterialIntegrability

/-!
# Positive physical decay gives actual weighted L² jets

The radial Leibniz formula adds the actual factor H^(-γ) to the finite
ordinary-to-material jet expansion. Any stronger positive physical decay
then supplies an integrable majorant for every fixed material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData}

/-- The fixed weight costs only its actual height power in each fixed
material derivative. The constant is independent of the field and point. -/
theorem n07a_materialPullback_mixedDerivative_bound
    (hT : IsMaterialData D T) (γ : ℝ) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : PolarPoint → ℝ),
      ContDiffOn ℝ ∞ f (annularOpen D) → ∀ (b : ℕ) (p : PolarPoint) (W : ℝ),
      0 ≤ W →
      (∀ j ≤ a, |mixedDerivative j b f (T.radius p.1, p.2)| ≤ W) →
      |mixedDerivative a b (materialPullback T γ f) p| ≤
        K * T.H (T.radius p.1) ^ (-γ) * W := by
  classical
  choose B hB hBb using fun i : Fin (a + 1) =>
    iteratedDeriv_materialH_rpow_bound hT (-γ) i.val
  choose P hP hPb using fun i : Fin (a + 1) =>
    n07a_materialPullback_zero_mixedDerivative_bound hT (a - i.val)
  let C : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i * P i
  have hC (i : Fin (a + 1)) : 0 ≤ C i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hP i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun f hf b p W hW hbound => ?_⟩
  have hH := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
  have hHpow : 0 ≤ T.H (T.radius p.1) ^ (-γ) := Real.rpow_nonneg hH.le _
  have hzero : ContDiff ℝ ∞ (materialPullback T 0 f) :=
    contDiff_materialPullback hT hf
  have he : materialPullback T γ f =
      fun q => T.H (T.radius q.1) ^ (-γ) * materialPullback T 0 f q := by
    funext q
    simp only [materialPullback, neg_zero, Real.rpow_zero, one_mul]
  rw [he, mixedDerivative_radial_mul (contDiff_materialH_rpow hT (-γ)) hzero]
  calc
    |∑ i : Fin (a + 1), (a.choose i.val : ℝ) *
        iteratedDeriv i.val (fun x => T.H (T.radius x) ^ (-γ)) p.1 *
          mixedDerivative (a - i.val) b (materialPullback T 0 f) p| ≤
      ∑ i : Fin (a + 1), |(a.choose i.val : ℝ) *
        iteratedDeriv i.val (fun x => T.H (T.radius x) ^ (-γ)) p.1 *
          mixedDerivative (a - i.val) b (materialPullback T 0 f) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (a + 1), C i * T.H (T.radius p.1) ^ (-γ) * W := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
      have hfbound := hPb i f hf b p W hW
        (fun j hj => hbound j (hj.trans (Nat.sub_le _ _)))
      calc
        _ ≤ ((a.choose i.val : ℝ) * (B i * T.H (T.radius p.1) ^ (-γ))) *
            (P i * W) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hBb i p.1) (Nat.cast_nonneg _))
            hfbound (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB i) hHpow))
        _ = C i * T.H (T.radius p.1) ^ (-γ) * W := by dsimp only [C]; ring
    _ = (∑ i, C i) * T.H (T.radius p.1) ^ (-γ) * W := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Actual ordinary spatial decay, with any fixed positive margin over
the requested weight, gives the actual weighted physical jet in L². -/
theorem n07a_weightedPhysicalJet_memLp_of_decay
    (hT : IsMaterialData D T) {γ δ : ℝ} (hγδ : γ < δ)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b c : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ (j : ℕ), j ≤ a → ∀ p : PolarPoint, p ∈ annularOpen D →
      |mixedDerivative j b f p| ≤ B * T.H p.1 ^ δ) :
    MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure := by
  obtain ⟨K, hK, hKb⟩ := n07a_materialPullback_mixedDerivative_bound hT γ a
  have hmajor := n07a_materialM_rpow_mul_H_rpow_cylinder_memLp hT (c : ℝ)
    (sub_pos.mpr hγδ)
  have hjetcont : Continuous (weightedPhysicalJet T γ a b c f) := by
    have hmc : Continuous (fun p : PolarPoint => T.M (T.radius p.1) ^ c) := by
      have hdata := hT
      obtain ⟨hsmooth, _, _, _, _, _, hradius, hinside, _⟩ := hdata
      exact (((hsmooth T.M (by simp)).continuousOn.comp_continuous
        (hradius.continuous.comp continuous_fst) (fun p => (hinside p.1).1)).pow c)
    exact hmc.mul (contDiff_mixedDerivative (contDiff_materialPullback hT hf) a b).continuous
  apply (hmajor.const_mul (K * B)).mono' hjetcont.aestronglyMeasurable
  filter_upwards [] with p
  have hp : (T.radius p.1, p.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩
  have hH := (hT.2.1 _ hp.1).2.1
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans (hT.2.1 _ hp.1).2.2.2
  have hj := hKb f hf b p (B * T.H (T.radius p.1) ^ δ)
    (mul_nonneg hB (Real.rpow_nonneg hH.le _))
    (fun j hj => hbound j hj _ hp)
  rw [Real.norm_eq_abs, weightedPhysicalJet, abs_mul,
    abs_of_nonneg (pow_nonneg hM c)]
  calc
    T.M (T.radius p.1) ^ c * |mixedDerivative a b (materialPullback T γ f) p| ≤
        T.M (T.radius p.1) ^ c *
          (K * T.H (T.radius p.1) ^ (-γ) * (B * T.H (T.radius p.1) ^ δ)) :=
      mul_le_mul_of_nonneg_left hj (pow_nonneg hM c)
    _ = (K * B) * (T.M (T.radius p.1) ^ (c : ℝ) *
        T.H (T.radius p.1) ^ (δ - γ)) := by
      rw [Real.rpow_natCast, sub_eq_add_neg, Real.rpow_add hH]
      ring

end ContinuousFlexibility.Analysis
