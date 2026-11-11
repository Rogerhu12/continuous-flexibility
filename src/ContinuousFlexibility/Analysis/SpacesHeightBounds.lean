import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import ContinuousFlexibility.Analysis.PhysicalJetBonding

/-!
# Quantitative point evaluation for the physical height grading

The four cylinder `L²` terms in the elementary Sobolev estimate are
coordinates of the order-two physical norm. This retains the linear
dependence on the height, needed for the physical compatibility integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- A concrete index for an ordinary material mixed derivative. -/
def spacesMixedJetIndex (a b s : ℕ) (h : a + b ≤ s) : JetIndex s :=
  ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, 0], by simpa using h⟩

@[simp] theorem spacesMixedJetIndex_radial (a b s : ℕ) (h : a + b ≤ s) :
    ((spacesMixedJetIndex a b s h).val 0).val = a := rfl

@[simp] theorem spacesMixedJetIndex_angular (a b s : ℕ) (h : a + b ≤ s) :
    ((spacesMixedJetIndex a b s h).val 1).val = b := rfl

@[simp] theorem spacesMixedJetIndex_weight (a b s : ℕ) (h : a + b ≤ s) :
    ((spacesMixedJetIndex a b s h).val 2).val = 0 := rfl

/-- Every actual jet norm is bounded by its physical Hilbert sum. -/
theorem spaces_weightedPhysicalJet_norm_le {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f)
    (s : ℕ) (j : JetIndex s) :
    (eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 materialCylinderMeasure).toReal ≤ physicalNorm T γ s f := by
  let a (k : JetIndex s) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (k.val 0).val (k.val 1).val (k.val 2).val f)
      2 materialCylinderMeasure
  have ha (k : JetIndex s) : a k ≠ ∞ := (hf.2.2.2.2 _ _ _).eLpNorm_ne_top
  have hsum : (∑ k : JetIndex s, a k ^ 2) ≠ ∞ := by
    exact ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.pow_ne_top (ha k))
  have hs : a j ^ 2 ≤ ∑ k : JetIndex s, a k ^ 2 :=
    Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ j)
  have hr : (a j).toReal ^ 2 ≤ (∑ k : JetIndex s, a k ^ 2).toReal := by
    simpa only [ENNReal.toReal_pow] using ENNReal.toReal_mono hsum hs
  change (a j).toReal ≤ Real.sqrt (∑ k : JetIndex s, a k ^ 2).toReal
  exact (Real.le_sqrt ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hr

theorem spaces_mixedDerivative_norm_le {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f)
    (a b s : ℕ) (h : a + b ≤ s) :
    (eLpNorm (mixedDerivative a b (materialPullback T γ f))
      2 materialCylinderMeasure).toReal ≤ physicalNorm T γ s f := by
  simpa only [spacesMixedJetIndex_radial, spacesMixedJetIndex_angular,
    spacesMixedJetIndex_weight, weightedPhysicalJet, pow_zero, one_mul] using
    spaces_weightedPhysicalJet_norm_le hf s (spacesMixedJetIndex a b s h)

/-- The normalized height is bounded everywhere by one fixed physical norm. -/
theorem spaces_materialPullback_bound {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) (p : PolarPoint) :
    |materialPullback T γ f p| ≤
      (4 * Real.sqrt Real.pi) * physicalNorm T γ 2 f := by
  have hs := contDiff_materialPullback hT hf.1
  have h00 : mixedDerivative 0 0 (materialPullback T γ f) = materialPullback T γ f := by
    funext q
    simp only [mixedDerivative, iteratedDeriv_zero]
  have hr : radialPartial (materialPullback T γ f) = mixedDerivative 1 0 (materialPullback T γ f) := by
    simpa only [h00] using radialPartial_mixedDerivative hs 0 0
  have ht : angularPartial (materialPullback T γ f) = mixedDerivative 0 1 (materialPullback T γ f) := by
    simpa only [h00] using angularPartial_mixedDerivative hs 0 0
  have hrt : radialPartial (angularPartial (materialPullback T γ f)) =
      mixedDerivative 1 1 (materialPullback T γ f) := by
    rw [ht]
    exact radialPartial_mixedDerivative hs 0 1
  have h := abs_le_materialCylinder_L2 hs
    (materialPullback_angular_periodic hf.2.2.1)
    (h00 ▸ heightMember_materialPullback_mixedDerivative_memLp hf 0 0)
    (by rw [hr]; exact heightMember_materialPullback_mixedDerivative_memLp hf 1 0)
    (by rw [ht]; exact heightMember_materialPullback_mixedDerivative_memLp hf 0 1)
    (by rw [hrt]; exact heightMember_materialPullback_mixedDerivative_memLp hf 1 1) p.1 p.2
  simp only [hr, ht, hrt] at h
  have h0 := spaces_mixedDerivative_norm_le hf 0 0 2 (by decide)
  rw [h00] at h0
  have h1 := spaces_mixedDerivative_norm_le hf 1 0 2 (by decide)
  have h2 := spaces_mixedDerivative_norm_le hf 0 1 2 (by decide)
  have h3 := spaces_mixedDerivative_norm_le hf 1 1 2 (by decide)
  calc
    |materialPullback T γ f p| ≤ _ := h
    _ ≤ Real.sqrt Real.pi * (physicalNorm T γ 2 f + physicalNorm T γ 2 f +
        physicalNorm T γ 2 f + physicalNorm T γ 2 f) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A positive exponent gives a uniform bound for the actual physical
height, including the regions where it is extended by zero. -/
theorem spaces_height_uniform_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      ∀ p : PolarPoint, |f p| ≤ C * physicalNorm T γ 2 f := by
  obtain ⟨_, hpos, _, _, _, _, _, hinv, hright, _, _, _, henv, _⟩ := hT
  obtain ⟨B, hB, hbound, _, _⟩ := henv 0 γ hγ
  refine ⟨B * (4 * Real.sqrt Real.pi), by positivity, fun f hf p => ?_⟩
  by_cases hp : p ∈ annularOpen D
  · have hH : 0 < T.H p.1 := (hpos p.1 hp.1).2.1
    have he : T.H p.1 ^ γ * materialPullback T γ f (T.rho p.1, p.2) = f p := by
      rw [materialPullback, hright p.1 hp.1, ← mul_assoc, ← Real.rpow_add hH,
        add_neg_cancel, Real.rpow_zero, one_mul]
    have hHbound : T.H p.1 ^ γ ≤ B := by
      simpa only [Real.rpow_zero, mul_one] using hbound p.1 hp.1
    rw [← he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH γ)]
    calc
      T.H p.1 ^ γ * |materialPullback T γ f (T.rho p.1, p.2)| ≤
          B * ((4 * Real.sqrt Real.pi) * physicalNorm T γ 2 f) :=
        mul_le_mul hHbound (spaces_materialPullback_bound hT hf _)
          (abs_nonneg _) hB.le
      _ = _ := by ring
  · rw [hf.2.2.2.1 p hp, abs_zero]
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

end ContinuousFlexibility.Statements
