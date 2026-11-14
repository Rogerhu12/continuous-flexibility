module

public import ContinuousFlexibility.Scalar.WeightedNormalizedMaterialJets
public import ContinuousFlexibility.Scalar.WeightedJetFamilies
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform control used by scalar composition estimates

The interpolation base and loss are fixed before the scalar function, the
low-norm radius, and the output order. The normalized material jets form an
actual jet family. On a low-norm ball, diagonal jet products have a linear
bound in one high input norm, and the decoded scalar range is bounded.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

def normalizedMaterialJetFamily
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) : MaterialJetFamily T A where
  jet := fun a b u => normalizedMaterialJet T γ a b (A.decode u)
  continuous := fun a b u =>
    (normalizedMaterialJet_contDiff hT (hA.2.2.2.1 u).1 a b).continuous
  pointwise := normalizedMaterialJet_decode_pointwise_bound hT hA
  weightedL2 := normalizedMaterialJet_decode_weightedL2_bound hT hA

/-- A diagonal specialization of the actual one-high product estimate. -/
def MaterialJetFamily.DiagonalEstimate
    {T : MaterialData} {A : SobolevModelData} (J : MaterialJetFamily T A)
    (base loss : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ k s : ℕ,
    ∀ (a b : Fin (k + 1) → ℕ) (c : ℕ),
    (∑ i, (a i + b i)) + c ≤ s →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (coefficient : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
      AEStronglyMeasurable coefficient materialCylinderMeasure →
      (∀ p, |coefficient p| ≤ K * T.M (T.radius p.1)) →
      ∀ u : A.Space, A.grading base u ≤ R →
        MemLp (materialFamilyMonomial J coefficient a b c (fun _ => u))
          2 materialCylinderMeasure ∧
        (eLpNorm (materialFamilyMonomial J coefficient a b c (fun _ => u))
          2 materialCylinderMeasure).toReal ≤ K * C * A.grading (s + loss) u

theorem MaterialJetFamily.exists_diagonalEstimate
    {D : ReferenceData} {T : MaterialData} {A : SobolevModelData}
    (hT : IsMaterialData D T) (J : MaterialJetFamily T A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ J.DiagonalEstimate base loss := by
  classical
  obtain ⟨base, loss, hbase, hbound⟩ := MaterialJetFamily.oneHigh hT J hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro R hR k s a b c horder
  obtain ⟨C, hC, hb⟩ := hbound k s a b c horder
  refine ⟨C * ((k + 1 : ℕ) : ℝ) * R ^ k, by positivity, ?_⟩
  intro coefficient K hK hc hcb u hu
  have h := hb coefficient K hK hc hcb (fun _ => u)
  refine ⟨h.1, ?_⟩
  have hprod (i : Fin (k + 1)) :
      (∏ j ∈ Finset.univ.erase i, A.grading base u) ≤ R ^ k := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, R :=
        Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hu)
      _ = R ^ k := by simp
  have hsum :
      (∑ i : Fin (k + 1), A.grading (s + loss) u *
        ∏ j ∈ Finset.univ.erase i, A.grading base u) ≤
        (((k + 1 : ℕ) : ℝ) * R ^ k) * A.grading (s + loss) u := by
    calc
      _ ≤ ∑ _i : Fin (k + 1), A.grading (s + loss) u * R ^ k :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hprod i) (apply_nonneg _ _))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact h.2.trans ((mul_le_mul_of_nonneg_left hsum (mul_nonneg hK hC)).trans_eq (by ring))

theorem decodedMaterialPullback_contDiff
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    ContDiff ℝ ∞ (fun p : PolarPoint => A.decode u (T.radius p.1, p.2)) :=
  contDiff_unweightedMaterialPullback hT (hA.2.2.2.1 u).1

/-- The actual unweighted decoded range is bounded on a fixed low-norm ball. -/
theorem decodedMaterialPullback_bound_of_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 ≤ γ)
    {base : ℕ} (hbase : 2 ≤ base) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : A.Space, A.grading base u ≤ R →
      ∀ p : PolarPoint, |A.decode u (T.radius p.1, p.2)| ≤ B := by
  obtain ⟨H, hH, hHb⟩ := materialH_nonnegative_power_bounded hT hγ
  obtain ⟨C, hC, hCb⟩ := normalizedMaterialJet_decode_pointwise_bound hT hA 0 0
  refine ⟨H * C * R, mul_nonneg (mul_nonneg hH hC) hR, fun u hu p => ?_⟩
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  have hj : |normalizedMaterialJet T γ 0 0 (A.decode u) p| ≤ C * R :=
    (hCb u p).trans (mul_le_mul_of_nonneg_left ((hp hbase u).trans hu) hC)
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  have hpositive : 0 < T.H (T.radius p.1) := (hpos _ (hinside p.1).1).2.1
  have heq : A.decode u (T.radius p.1, p.2) =
      T.H (T.radius p.1) ^ γ * normalizedMaterialJet T γ 0 0 (A.decode u) p := by
    simp only [normalizedMaterialJet, mixedDerivative, iteratedDeriv_zero]
    rw [← mul_assoc, ← Real.rpow_add hpositive, add_neg_cancel, Real.rpow_zero, one_mul]
  rw [heq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpositive γ)]
  exact (mul_le_mul (hHb p.1) hj (abs_nonneg _) hH).trans_eq (by ring)

theorem scalar_iteratedDeriv_bound_on_interval {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, |z| ≤ B → |iteratedDeriv n F z| ≤ K := by
  have hn : ContDiff ℝ ∞ (iteratedDeriv n F) := by
    rw [iteratedDeriv_eq_iterate]
    exact hF.iterate_deriv n
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (-B) B)).bddAbove_image
    hn.continuous.abs.continuousOn
  refine ⟨max 0 K, le_max_left _ _, fun z hz => ?_⟩
  exact (hK ⟨z, abs_le.mp hz, rfl⟩).trans (le_max_right _ _)

/-- The mean value estimate exposes one actual input factor at order zero. -/
theorem scalar_zero_value_and_quotient_bound {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, |z| ≤ B →
      |F z| ≤ K * |z| ∧ |F z / z| ≤ K := by
  obtain ⟨K, hK, hKb⟩ := scalar_iteratedDeriv_bound_on_interval hF 1 B
  refine ⟨K, hK, fun z hz => ?_⟩
  have hv : |F z| ≤ K * |z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ Icc (-B) B) => hF.differentiable (by simp) x)
      (fun x (hx : x ∈ Icc (-B) B) => by
        simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hKb x (abs_le.mpr hx))
      (convex_Icc (-B) B) (show (0 : ℝ) ∈ Icc (-B) B from ⟨neg_nonpos.mpr hB, hB⟩)
      (abs_le.mp hz)
    simpa only [hF0, sub_zero, Real.norm_eq_abs] using h
  refine ⟨hv, ?_⟩
  by_cases hzero : z = 0
  · simpa only [hzero, div_zero, abs_zero] using hK
  · rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hzero)).mpr hv

/-- Finite sums retain the sum of their actual L² bounds. -/
theorem scalar_finiteL2_sum_bound {ι : Type*} [Fintype ι]
    (f : ι → PolarPoint → ℝ) (C : ι → ℝ) (N : ℝ)
    (hf : ∀ i, MemLp (f i) 2 materialCylinderMeasure)
    (hbound : ∀ i, (eLpNorm (f i) 2 materialCylinderMeasure).toReal ≤ C i * N) :
    MemLp (∑ i, f i) 2 materialCylinderMeasure ∧
      (eLpNorm (∑ i, f i) 2 materialCylinderMeasure).toReal ≤ (∑ i, C i) * N := by
  classical
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => hf i), ?_⟩
  have hfinite : (∑ i, eLpNorm (f i) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (hf i).eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := f) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun i _ => (hf i).eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => hbound i)

end ContinuousFlexibility.Statements
