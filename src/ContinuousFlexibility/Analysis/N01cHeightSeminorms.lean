import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Quantitative height evaluation bounds for N01c

The local cylinder estimate already bounds a point by four global `L²`
norms. Here each of those norms is bounded by the actual finite-jet norm,
and then by the grading of any realization satisfying `IsSobolevModel`.
The constant is explicit, independent of the height and the evaluation
point, and the loss is exactly two material derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

/-- One actual weighted jet is bounded by the finite physical jet norm. -/
theorem weightedPhysicalJet_L2_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) {a b c s : ℕ} (habc : a + b + c ≤ s) :
    (eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
  let j : JetIndex s :=
    ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using habc⟩
  let term (i : JetIndex s) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (i.val 0).val (i.val 1).val (i.val 2).val f)
      2 materialCylinderMeasure ^ 2
  have hfinite : (∑ i : JetIndex s, term i) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact ENNReal.pow_lt_top
      (hf.2.2.2.2 (i.val 0).val (i.val 1).val (i.val 2).val).eLpNorm_ne_top.lt_top
  have hsingle : term j ≤ ∑ i : JetIndex s, term i :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)
  have hreal := ENNReal.toReal_mono hfinite.ne hsingle
  have hsq : (eLpNorm (weightedPhysicalJet T γ a b c f)
      2 materialCylinderMeasure).toReal ^ 2 ≤ (∑ i : JetIndex s, term i).toReal := by
    simpa only [term, j, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ENNReal.toReal_pow] using hreal
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq ENNReal.toReal_nonneg] at hroot
  exact hroot

/-- The unweighted material-coordinate jet is the weight-zero physical jet. -/
theorem materialMixedDerivative_L2_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) {a b s : ℕ} (hab : a + b ≤ s) :
    (eLpNorm (mixedDerivative a b (materialPullback T γ f))
      2 materialCylinderMeasure).toReal ≤ physicalNorm T γ s f := by
  have hjet : weightedPhysicalJet T γ a b 0 f =
      mixedDerivative a b (materialPullback T γ f) := by
    funext p
    simp only [weightedPhysicalJet, pow_zero, one_mul]
  rw [← hjet]
  exact weightedPhysicalJet_L2_le_physicalNorm hf (by omega)

/-- Two additional material derivatives give point evaluation with one
uniform constant. The output derivative orders may be below the chosen
norm order; there is no hidden constant depending on the input function. -/
theorem heightMember_materialPullback_mixedDerivative_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    {a b s : ℕ} (hab : a + b + 2 ≤ s) (p : PolarPoint) :
    |mixedDerivative a b (materialPullback T γ f) p| ≤
      (4 * Real.sqrt Real.pi) * physicalNorm T γ s f := by
  let F : PolarPoint → ℝ := materialPullback T γ f
  let g : PolarPoint → ℝ := mixedDerivative a b F
  have hF : ContDiff ℝ ∞ F := contDiff_materialPullback hT hf.1
  have hg : ContDiff ℝ ∞ g := contDiff_mixedDerivative hF a b
  have hperiodic : ∀ x : ℝ, Function.Periodic (fun θ => g (x, θ)) Real.pi :=
    mixedDerivative_angular_periodic
      (materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1) a b
  have hx : radialPartial g = mixedDerivative (a + 1) b F :=
    radialPartial_mixedDerivative hF a b
  have ht : angularPartial g = mixedDerivative a (b + 1) F :=
    angularPartial_mixedDerivative hF a b
  have hxt : radialPartial (angularPartial g) = mixedDerivative (a + 1) (b + 1) F := by
    rw [ht, radialPartial_mixedDerivative hF a (b + 1)]
  have hm0 : MemLp g 2 materialCylinderMeasure :=
    heightMember_materialPullback_mixedDerivative_memLp hf a b
  have hm1 : MemLp (radialPartial g) 2 materialCylinderMeasure := by
    rw [hx]
    exact heightMember_materialPullback_mixedDerivative_memLp hf (a + 1) b
  have hm2 : MemLp (angularPartial g) 2 materialCylinderMeasure := by
    rw [ht]
    exact heightMember_materialPullback_mixedDerivative_memLp hf a (b + 1)
  have hm3 : MemLp (radialPartial (angularPartial g)) 2 materialCylinderMeasure := by
    rw [hxt]
    exact heightMember_materialPullback_mixedDerivative_memLp hf (a + 1) (b + 1)
  have h0 : (eLpNorm g 2 materialCylinderMeasure).toReal ≤ physicalNorm T γ s f :=
    materialMixedDerivative_L2_le_physicalNorm hf (by omega)
  have h1 : (eLpNorm (radialPartial g) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
    rw [hx]
    exact materialMixedDerivative_L2_le_physicalNorm hf (by omega)
  have h2 : (eLpNorm (angularPartial g) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
    rw [ht]
    exact materialMixedDerivative_L2_le_physicalNorm hf (by omega)
  have h3 : (eLpNorm (radialPartial (angularPartial g)) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
    rw [hxt]
    exact materialMixedDerivative_L2_le_physicalNorm hf (by omega)
  calc
    |g p| ≤ Real.sqrt Real.pi *
        ((eLpNorm g 2 materialCylinderMeasure).toReal +
          (eLpNorm (radialPartial g) 2 materialCylinderMeasure).toReal +
          (eLpNorm (angularPartial g) 2 materialCylinderMeasure).toReal +
          (eLpNorm (radialPartial (angularPartial g)) 2 materialCylinderMeasure).toReal) :=
      abs_le_materialCylinder_L2 hg hperiodic hm0 hm1 hm2 hm3 p.1 p.2
    _ ≤ Real.sqrt Real.pi *
        (physicalNorm T γ s f + physicalNorm T γ s f +
          physicalNorm T γ s f + physicalNorm T γ s f) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)
        (Real.sqrt_nonneg _)
    _ = (4 * Real.sqrt Real.pi) * physicalNorm T γ s f := by ring

/-- A realization's physical norm is bounded by its actual projective grading. -/
theorem sobolevModel_physicalNorm_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hM : IsSobolevModel D T γ M) (u : M.Space) {s t : ℕ} (hst : s ≤ t) :
    physicalNorm T γ s (M.decode u) ≤ M.grading t u := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hM
  rw [← hnorm u s]
  exact norm_coordinate_le_graded (fun n => M.level n) M.bond hst u

/-- Quantitative material-jet evaluation on the realized height space. -/
theorem sobolevModel_materialPullback_mixedDerivative_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (u : M.Space) {a b s : ℕ} (hab : a + b + 2 ≤ s) (p : PolarPoint) :
    |mixedDerivative a b (materialPullback T γ (M.decode u)) p| ≤
      (4 * Real.sqrt Real.pi) * M.grading s u := by
  have hu : HeightMember D T γ (M.decode u) := hM.2.2.2.1 u
  exact (heightMember_materialPullback_mixedDerivative_le_physicalNorm hT hu hab p).trans
    (mul_le_mul_of_nonneg_left (sobolevModel_physicalNorm_le_grading hM u le_rfl)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- Returning from the material coordinate restores exactly the prescribed
height weight. This estimate is uniform over the entire open annulus. -/
theorem sobolevModel_decode_pointwise_weighted_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (u : M.Space) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    |M.decode u p| ≤ (4 * Real.sqrt Real.pi) * M.grading 2 u * T.H p.1 ^ γ := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, hinv, _⟩ := hdata
  have hH : 0 < T.H p.1 := (hpos p.1 hp.1).2.1
  have hbound := sobolevModel_materialPullback_mixedDerivative_le_grading
    hT hM u (a := 0) (b := 0) (s := 2) (by norm_num) (T.rho p.1, p.2)
  simp only [mixedDerivative, iteratedDeriv_zero, materialPullback, hinv p.1 hp.1] at hbound
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH (-γ)),
    Real.rpow_neg hH.le, ← div_eq_inv_mul] at hbound
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hH γ)).mp hbound

end ContinuousFlexibility.Statements
