import ContinuousFlexibility.Statements.ScalarWeighted
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Quantitative pointwise bounds for the scalar weighted space

The bounds here retain the actual input seminorm.  In particular the constants
are independent of the height, as required when choosing one common scalar
state neighbourhood.  An existential bound for each individual height would
not suffice for that purpose.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Every summand of the actual physical norm is bounded by that norm. -/
theorem weightedPhysicalJet_norm_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) {a b c s : ℕ} (h : a + b + c ≤ s) :
    (eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
  let j : JetIndex s :=
    ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using h⟩
  let N (i : JetIndex s) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (i.val 0).val (i.val 1).val (i.val 2).val f)
      2 materialCylinderMeasure
  have hN (i : JetIndex s) : N i ≠ (⊤ : ℝ≥0∞) :=
    (hf.2.2.2.2 (i.val 0).val (i.val 1).val (i.val 2).val).eLpNorm_ne_top
  have hsum : (∑ i : JetIndex s, N i ^ 2) ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.pow_ne_top (hN i)
  apply Real.le_sqrt_of_sq_le
  have hle : N j ^ 2 ≤ ∑ i : JetIndex s, N i ^ 2 :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
  have hr := ENNReal.toReal_mono hsum hle
  simpa only [ENNReal.toReal_pow] using hr

/-- A physical norm is bounded by the specified increasing projective grading. -/
theorem physicalNorm_decode_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hA : IsSobolevModel D T γ A) (u : A.Space) (s : ℕ) :
    physicalNorm T γ s (A.decode u) ≤ A.grading s u := by
  rw [← hA.2.2.2.2.2.2.2 u s]
  exact norm_coordinate_le_graded (fun s => A.level s) A.bond le_rfl u

/-- The four cylinder norms needed for a mixed jet are controlled by one
physical input seminorm, at two additional orders. -/
theorem materialPullback_mixedDerivative_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (materialPullback T γ f) p| ≤
      (4 * Real.sqrt Real.pi) * physicalNorm T γ (a + b + 2) f := by
  let F : PolarPoint → ℝ := materialPullback T γ f
  let g : PolarPoint → ℝ := mixedDerivative a b F
  have hF : ContDiff ℝ ∞ F := contDiff_materialPullback hT hf.1
  have hg : ContDiff ℝ ∞ g := contDiff_mixedDerivative hF a b
  have hp : ∀ r : ℝ, Function.Periodic (fun θ => g (r, θ)) Real.pi :=
    mixedDerivative_angular_periodic (g := F)
      (materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1) a b
  have hx : radialPartial g = mixedDerivative (a + 1) b F :=
    radialPartial_mixedDerivative hF a b
  have ht : angularPartial g = mixedDerivative a (b + 1) F :=
    angularPartial_mixedDerivative hF a b
  have hxt : radialPartial (angularPartial g) = mixedDerivative (a + 1) (b + 1) F := by
    rw [ht, radialPartial_mixedDerivative hF a (b + 1)]
  have hmem (i j : ℕ) : MemLp (mixedDerivative i j F) 2 materialCylinderMeasure :=
    heightMember_materialPullback_mixedDerivative_memLp hf i j
  have hbound (i j : ℕ) (hij : i + j ≤ a + b + 2) :
      (eLpNorm (mixedDerivative i j F) 2 materialCylinderMeasure).toReal ≤
        physicalNorm T γ (a + b + 2) f := by
    have he : weightedPhysicalJet T γ i j 0 f = mixedDerivative i j F := by
      funext p
      simp only [weightedPhysicalJet, pow_zero, one_mul]
    have h := weightedPhysicalJet_norm_le_physicalNorm hf (a := i) (b := j) (c := 0)
      (s := a + b + 2) (by omega)
    rw [he] at h
    exact h
  have hm1 : MemLp (radialPartial g) 2 materialCylinderMeasure := by
    rw [hx]
    exact hmem (a + 1) b
  have hm2 : MemLp (angularPartial g) 2 materialCylinderMeasure := by
    rw [ht]
    exact hmem a (b + 1)
  have hm3 : MemLp (radialPartial (angularPartial g)) 2 materialCylinderMeasure := by
    rw [hxt]
    exact hmem (a + 1) (b + 1)
  have hb := abs_le_materialCylinder_L2 hg hp (hmem a b) hm1 hm2 hm3 p.1 p.2
  rw [hx, hxt, ht] at hb
  calc
    _ ≤ Real.sqrt Real.pi *
        ((eLpNorm g 2 materialCylinderMeasure).toReal +
          (eLpNorm (mixedDerivative (a + 1) b F) 2 materialCylinderMeasure).toReal +
          (eLpNorm (mixedDerivative a (b + 1) F) 2 materialCylinderMeasure).toReal +
          (eLpNorm (mixedDerivative (a + 1) (b + 1) F) 2 materialCylinderMeasure).toReal) := hb
    _ ≤ Real.sqrt Real.pi *
        (physicalNorm T γ (a + b + 2) f + physicalNorm T γ (a + b + 2) f +
          physicalNorm T γ (a + b + 2) f + physicalNorm T γ (a + b + 2) f) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add (hbound a b (by omega))
          (hbound (a + 1) b (by omega))) (hbound a (b + 1) (by omega)))
          (hbound (a + 1) (b + 1) (by omega))) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Uniform evaluation control on the actual decoded Sobolev model. -/
theorem materialPullback_decode_mixedDerivative_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (u : A.Space) (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (materialPullback T γ (A.decode u)) p| ≤
      (4 * Real.sqrt Real.pi) * A.grading (a + b + 2) u :=
  (materialPullback_mixedDerivative_le_physicalNorm hT (hA.2.2.2.1 u) a b p).trans
    (mul_le_mul_of_nonneg_left (physicalNorm_decode_le_grading hA u (a + b + 2))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

end ContinuousFlexibility.Statements
