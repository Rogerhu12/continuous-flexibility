import ContinuousFlexibility.Scalar.WeightedWeightShiftJets
import ContinuousFlexibility.Scalar.WeightedOrdinaryPointwise

/-!
# Normalized material jets of actual decoded heights

Differentiation here is applied to the unweighted material pullback before
multiplication by H^(-γ). The radial Leibniz formula expresses each such jet
as a finite sum of jets of the weighted pullback, with bounded coefficients.
The weighted L² estimate preserves the total jet order, while evaluation
uses the same two additional orders as the cylinder pointwise estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The actual unweighted material jet, normalized after differentiation. -/
def normalizedMaterialJet (T : MaterialData) (γ : ℝ) (a b : ℕ)
    (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  T.H (T.radius p.1) ^ (-γ) *
    mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p

theorem normalizedMaterialJet_contDiff
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (a b : ℕ) :
    ContDiff ℝ ∞ (normalizedMaterialJet T γ a b f) := by
  have hu : ContDiff ℝ ∞ (fun p : PolarPoint => f (T.radius p.1, p.2)) := by
    simpa only [materialPullback, neg_zero, Real.rpow_zero, one_mul] using
      contDiff_materialPullback (γ := 0) hT hf
  exact ((contDiff_materialH_rpow hT (-γ)).comp contDiff_fst).mul
    (contDiff_mixedDerivative hu a b)

/-- The mixed derivative of the unweighted material pullback is the actual
material radial derivative of the physical angular slice. -/
theorem mixedDerivative_comp_materialRadius
    {D : ReferenceData} {T : MaterialData} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p =
      materialDerivativeIterate T a
        (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) (T.radius p.1) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, p.2)) :=
    contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun r : ℝ => (r, p.2)) (Ioo D.a D.b) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  have hg : ContDiffOn ℝ ∞
      (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) (Ioo D.a D.b) := by
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 b).comp hs.contDiffOn hm
  exact iteratedDeriv_comp_materialRadius hT hg a p.1

/-- Every actual normalized decoded jet has a uniform evaluation bound at
its order plus the two cylinder Sobolev orders. -/
theorem normalizedMaterialJet_decode_pointwise_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.Space) (p : PolarPoint),
      |normalizedMaterialJet T γ a b (A.decode u) p| ≤ C * A.grading (a + b + 2) u := by
  obtain ⟨C, hC, hbound⟩ := materialDerivative_decode_angular_slice_le_grading hT hA a b
  refine ⟨C, hC, fun u p => ?_⟩
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  have hH : 0 < T.H (T.radius p.1) := (hpos _ (hinside p.1).1).2.1
  have hcancel : T.H (T.radius p.1) ^ (-γ) * T.H (T.radius p.1) ^ γ = 1 := by
    rw [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero]
  rw [normalizedMaterialJet,
    mixedDerivative_comp_materialRadius hT (hA.2.2.2.1 u).1 a b p,
    abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH (-γ))]
  calc
    _ ≤ T.H (T.radius p.1) ^ (-γ) *
        (C * T.H (T.radius p.1) ^ γ * A.grading (a + b + 2) u) :=
      mul_le_mul_of_nonneg_left
        (hbound u p.2 (T.radius p.1) (hinside p.1).1) (Real.rpow_nonneg hH.le _)
    _ = C * (T.H (T.radius p.1) ^ (-γ) * T.H (T.radius p.1) ^ γ) *
        A.grading (a + b + 2) u := by ring
    _ = C * A.grading (a + b + 2) u := by rw [hcancel, mul_one]

/-- Each weighted normalized material jet belongs to L² and is bounded by
the physical norm at exactly the same total order. -/
theorem normalizedMaterialJet_weightedL2_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (fun p => T.M (T.radius p.1) ^ c * normalizedMaterialJet T γ a b f p)
        2 materialCylinderMeasure ∧
      (eLpNorm (fun p => T.M (T.radius p.1) ^ c * normalizedMaterialJet T γ a b f p)
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c) f := by
  classical
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hdata
  have hH (x : ℝ) : 0 < T.H (T.radius x) := (hpos _ (hinside x).1).2.1
  let F : ℝ → ℝ := fun x => T.H (T.radius x) ^ γ
  have hF : ContDiff ℝ ∞ F := contDiff_materialH_rpow hT γ
  choose B hB hBx using fun i : Fin (a + 1) =>
    iteratedDeriv_materialH_rpow_bound hT γ i.val
  let C : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i
  have hC (i : Fin (a + 1)) : 0 ≤ C i := mul_nonneg (Nat.cast_nonneg _) (hB i)
  let coefficient : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    (a.choose i.val : ℝ) * T.H (T.radius p.1) ^ (-γ) * iteratedDeriv i.val F p.1
  have hcancel (x : ℝ) : T.H (T.radius x) ^ (-γ) * T.H (T.radius x) ^ γ = 1 := by
    rw [← Real.rpow_add (hH x), neg_add_cancel, Real.rpow_zero]
  have hc (i : Fin (a + 1)) :
      AEStronglyMeasurable (coefficient i) materialCylinderMeasure := by
    have hi : ContDiff ℝ ∞ (iteratedDeriv i.val F) := by
      rw [iteratedDeriv_eq_iterate]
      exact hF.iterate_deriv i.val
    have hd : ContDiff ℝ ∞ (fun p : PolarPoint => iteratedDeriv i.val F p.1) :=
      hi.comp contDiff_fst
    have hn : ContDiff ℝ ∞ (fun p : PolarPoint => T.H (T.radius p.1) ^ (-γ)) :=
      (contDiff_materialH_rpow hT (-γ)).comp contDiff_fst
    exact ((contDiff_const.mul hn).mul hd).continuous.aestronglyMeasurable
  have hcb (i : Fin (a + 1)) (p : PolarPoint) : |coefficient i p| ≤ C i := by
    dsimp only [coefficient, C]
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val)),
      abs_of_pos (Real.rpow_pos_of_pos (hH p.1) (-γ))]
    calc
      _ ≤ (a.choose i.val : ℝ) * T.H (T.radius p.1) ^ (-γ) *
          (B i * T.H (T.radius p.1) ^ γ) :=
        mul_le_mul_of_nonneg_left (hBx i p.1)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hH p.1).le _))
      _ = ((a.choose i.val : ℝ) * B i) *
          (T.H (T.radius p.1) ^ (-γ) * T.H (T.radius p.1) ^ γ) := by ring
      _ = (a.choose i.val : ℝ) * B i := by rw [hcancel, mul_one]
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro f hf
  let term : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    coefficient i p * weightedPhysicalJet T γ (a - i.val) b c f p
  have ht (i : Fin (a + 1)) := weightedPhysicalJet_mul_coefficient_bound hT hf
    (a - i.val) b c 0 (a + b + c) (by omega) (hC i) (hc i)
    (fun p => by simpa only [pow_zero, mul_one] using hcb i p)
  have hrestore : (fun p : PolarPoint => f (T.radius p.1, p.2)) =
      fun p => F p.1 * materialPullback T γ f p := by
    funext p
    dsimp only [F, materialPullback]
    rw [← mul_assoc, ← Real.rpow_add (hH p.1), add_neg_cancel, Real.rpow_zero, one_mul]
  have heq :
      (fun p => T.M (T.radius p.1) ^ c * normalizedMaterialJet T γ a b f p) =
        ∑ i : Fin (a + 1), term i := by
    funext p
    change T.M (T.radius p.1) ^ c *
      (T.H (T.radius p.1) ^ (-γ) *
        mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p) = _
    rw [hrestore, mixedDerivative_radial_mul hF (contDiff_materialPullback hT hf.1)]
    simp only [Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [term, coefficient, weightedPhysicalJet]
    ring
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => (ht i).1), ?_⟩
  have hfinite : (∑ i, eLpNorm (term i) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (ht i).1.eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := term) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun i _ => (ht i).1.eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => (ht i).2)

/-- The same-order L² bound in the actual decoded projective grading. -/
theorem normalizedMaterialJet_decode_weightedL2_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      MemLp (fun p => T.M (T.radius p.1) ^ c * normalizedMaterialJet T γ a b (A.decode u) p)
        2 materialCylinderMeasure ∧
      (eLpNorm (fun p => T.M (T.radius p.1) ^ c *
        normalizedMaterialJet T γ a b (A.decode u) p) 2 materialCylinderMeasure).toReal ≤
          C * A.grading (a + b + c) u := by
  obtain ⟨C, hC, hbound⟩ := normalizedMaterialJet_weightedL2_bound (γ := γ) hT a b c
  refine ⟨C, hC, fun u => ?_⟩
  have hb := hbound (A.decode u) (hA.2.2.2.1 u)
  exact ⟨hb.1, hb.2.trans
    (mul_le_mul_of_nonneg_left (physicalNorm_decode_le_grading hA u (a + b + c)) hC)⟩

end ContinuousFlexibility.Statements
