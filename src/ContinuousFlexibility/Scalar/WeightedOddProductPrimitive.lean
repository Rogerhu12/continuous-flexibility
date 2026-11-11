import ContinuousFlexibility.Scalar.WeightedAngularProductJets
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# The actual even primitive of an odd angular product

A positive-weight decoded height is globally smooth. The product of an even
height and the angular derivative of another is smooth, odd, periodic, and
supported in the physical core. Its prescribed angular primitive is therefore
an actual even height member. The primitive and the return from the sum weight
to the original weight preserve the one-high-factor estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

def scalarOddProductPrimitive (f g : PolarPoint → ℝ) : PolarPoint → ℝ :=
  scalarAngularPrimitive (scalarAngularProduct f g)

theorem scalarAngularProduct_contDiff {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scalarAngularProduct f g) :=
  hf.mul (contDiff_iff_contDiffAt.mpr fun p =>
    contDiffAt_angularPartial hg.contDiffAt (by simp))

theorem scalarAngularProduct_weightedJets_memLp
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (u : Fin 2 → A.Space)
    (a b c : ℕ) :
    MemLp (weightedPhysicalJet T (2 * γ) a b c
      (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))))
      2 materialCylinderMeasure := by
  obtain ⟨_, _, _, hjets⟩ := scalarAngularProduct_weightedJets_oneHigh hT hA hinterp
  obtain ⟨_, _, hbound⟩ := hjets (a + b + c) a b c le_rfl
  exact (hbound u).1

/-- Sum the actual weighted jets without changing their common loss. -/
theorem scalarAngularProduct_sumWeight_physicalNorm_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin 2 → A.Space,
        physicalNorm T (2 * γ) s
          (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  classical
  obtain ⟨base, loss, hbase, hjets⟩ := scalarAngularProduct_weightedJets_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro s
  have hj (j : JetIndex s) :=
    hjets s (j.val 0).val (j.val 1).val (j.val 2).val j.property
  choose B hB hBu using hj
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, ?_⟩
  intro u
  let N : ℝ := ∑ i, A.grading (s + loss) (u i) *
    ∏ j ∈ Finset.univ.erase i, A.grading base (u j)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)))
  have hjet (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T (2 * γ) a b c
        (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))))
        2 materialCylinderMeasure).toReal ≤ K * N := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj' :
        (eLpNorm (weightedPhysicalJet T (2 * γ) a b c
          (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))))
          2 materialCylinderMeasure).toReal ≤ B j * N := by
      simpa [j, N] using (hBu j u).2
    exact hj'.trans (mul_le_mul_of_nonneg_right (hBK j) hN)
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN)
    (fun a b c _ => scalarAngularProduct_weightedJets_memLp hT hA hinterp u a b c)
    hjet).trans_eq (by dsimp only [N]; ring)

/-- The primitive belongs to the sum-weight space by its actual parity,
period, support and square-integrable weighted jets. -/
theorem scalarOddProductPrimitive_sumWeight_heightMember
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    (u : Fin 2 → A.Space) :
    HeightMember D T (2 * γ)
      (scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1))) := by
  have hu (i : Fin 2) := hA.2.2.2.1 (u i)
  have hc (i : Fin 2) : ContDiff ℝ ∞ (A.decode (u i)) :=
    (heightMember_contDiff_and_flatJets hT hγ (hu i)).1
  have hθ : ∀ r θ, angularPartial (A.decode (u 1)) (r, -θ) =
      -angularPartial (A.decode (u 1)) (r, θ) := by
    simpa only [neg_one_mul] using scalar_angularPartial_reflection (σ := 1) (hu 1).1
      (fun r θ => by simpa only [one_mul] using (hu 1).2.1 r θ) (hu 1).2.2.2.1
  apply scalarAngularPrimitive_heightMember hT (scalarAngularProduct_contDiff (hc 0) (hc 1))
  · intro r θ
    dsimp only [scalarAngularProduct]
    rw [(hu 0).2.1 r θ, hθ r θ]
    ring
  · intro p
    dsimp only [scalarAngularProduct]
    rw [(hu 0).2.2.1 p, periodic_angularPartial (hu 1).2.2.1 p]
  · intro p hp
    dsimp only [scalarAngularProduct]
    rw [(hu 0).2.2.2.1 p hp, zero_mul]
  · exact scalarAngularProduct_weightedJets_memLp hT hA hinterp u

theorem scalarOddProductPrimitive_heightMember
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    (u : Fin 2 → A.Space) :
    HeightMember D T γ
      (scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1))) :=
  heightMember_weight_shift hT (by linarith : γ ≤ 2 * γ)
    (scalarOddProductPrimitive_sumWeight_heightMember hT hA hinterp hγ u)

/-- The genuine angular primitive has one fixed loss in the original
positive-weight space, chosen before every output order. -/
theorem scalarOddProductPrimitive_physicalNorm_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin 2 → A.Space,
        physicalNorm T γ s
          (scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1))) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hproduct⟩ :=
    scalarAngularProduct_sumWeight_physicalNorm_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro s
  obtain ⟨C, hC, hCu⟩ := hproduct s
  obtain ⟨K, hK, hKf⟩ := physicalNorm_weight_shift_bound hT
    (by linarith : γ ≤ 2 * γ) s
  let P : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ) * Real.pi
  have hP : 0 ≤ P := mul_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  refine ⟨K * (P * C), mul_nonneg hK (mul_nonneg hP hC), ?_⟩
  intro u
  have hc (i : Fin 2) : ContDiff ℝ ∞ (A.decode (u i)) :=
    (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 (u i))).1
  have hp := scalarAngularPrimitive_physicalNorm_le hT
    (scalarAngularProduct_contDiff (hc 0) (hc 1))
    (scalarAngularProduct_weightedJets_memLp hT hA hinterp u) s
  have hw := hKf _ (scalarOddProductPrimitive_sumWeight_heightMember hT hA hinterp hγ u)
  exact (hw.trans (mul_le_mul_of_nonneg_left
    (hp.trans (mul_le_mul_of_nonneg_left (hCu u) hP)) hK)).trans_eq (by ring)

end ContinuousFlexibility.Statements
