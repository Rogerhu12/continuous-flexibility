import ContinuousFlexibility.Radial.ReferenceGraphProjection

/-!
# Arbitrary angular bands preserve the actual physical reference graph

The mean mode controls the left asymptotic constant.  The first positive
cosine mode controls both the border row and its scalar coefficient.
Consequently an arbitrary finite projection preserves the genuine weak
graph when those scalar components are projected onto their own modes.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem n07a_referenceBasisProjection_lift (I : Finset ℕ) (n : ℕ)
    (a : ℝ → ℝ) :
    referenceBasisProjection I (fun x : PolarPoint => a x.1 * referenceAngularBasis n x.2) =
      (fun x : PolarPoint => if n ∈ I then a x.1 * referenceAngularBasis n x.2 else 0) := by
  by_cases hn : n ∈ I
  · simpa only [ite_eq_left hn] using referenceBasisProjection_lift I hn a
  · funext x
    simp only [ite_eq_right hn, referenceBasisProjection, angularBasisProjection]
    apply Finset.sum_eq_zero
    intro k hk
    have hc : referenceAngularCoefficient
        (fun θ => a x.1 * referenceAngularBasis n θ) k =
        if k = n then a x.1 else 0 := by
      simpa only [Finset.sum_singleton, Finset.mem_singleton] using
        referenceAngularCoefficient_sum_basis {n} (fun _ => a x.1) k
    have hkn : k ≠ n := fun h => hn (h ▸ hk)
    rw [hc, ite_eq_right hkn, zero_mul]

theorem n07a_angularBasisProjection_const (I : Finset ℕ) (c : ℝ) :
    angularBasisProjection I (fun _ => c) = fun _ => if 0 ∈ I then c else 0 := by
  funext θ
  have h := congrFun (n07a_referenceBasisProjection_lift I 0 (fun _ => c)) (0, θ)
  simpa only [referenceBasisProjection, referenceAngularBasis, mul_one] using h

theorem n07a_referenceBasisProjection_mean (I : Finset ℕ)
    (u : PolarPoint → ℝ) (r : ℝ) :
    radialAngularMean (fun θ => referenceBasisProjection I u (r, θ)) =
      if 0 ∈ I then radialAngularMean (fun θ => u (r, θ)) else 0 := by
  simpa only [referenceAngularCoefficient_zero, referenceBasisProjection] using
    referenceAngularCoefficient_projection I (fun θ => u (r, θ)) 0

theorem n07a_referenceBasisProjection_column (I : Finset ℕ) (D : ReferenceData) :
    referenceBasisProjection I
      (fun x : PolarPoint => referenceColumn D x.1 * cosineMode 2 x.2) =
      (fun x : PolarPoint => if 1 ∈ I then referenceColumn D x.1 * cosineMode 2 x.2 else 0) :=
  n07a_referenceBasisProjection_lift I 1 (referenceColumn D)

theorem n07a_referenceBasisProjection_row (I : Finset ℕ) (D : ReferenceData)
    (u : PolarPoint → ℝ) :
    referenceRow D (referenceBasisProjection I u) =
      if 1 ∈ I then referenceRow D u else 0 := by
  have he : referenceMode (referenceBasisProjection I u) 2 =
      fun r => if 1 ∈ I then referenceMode u 2 r else 0 := by
    funext r
    exact referenceAngularCoefficient_projection I (fun θ => u (r, θ)) 1
  unfold referenceRow
  rw [he]
  by_cases h1 : 1 ∈ I
  · simp only [ite_eq_left h1]
  · simp only [ite_eq_right h1, mul_zero, intervalIntegral.integral_zero]

theorem n07a_referenceBasisProjection_remainder_ae {D : ReferenceData}
    (hpart : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (I : Finset ℕ) (μ : ℝ) :
    referenceBasisProjection I (outputRemainder D aL U) =ᵐ[radialPhysicalMeasure D]
      outputRemainder D (if 0 ∈ I then aL else 0) (referenceBasisProjection I U.1, μ) := by
  have hs : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ θ,
      referenceBasisProjection I (outputRemainder D aL U) (r, θ) =
        outputRemainder D (if 0 ∈ I then aL else 0)
          (referenceBasisProjection I U.1, μ) (r, θ) := by
    filter_upwards [hU.1.ae_angular_memLp hpart] with r hr
    have hc : MemLp (fun _ : ℝ => aL * D.chiLeft r) 2
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
      memLp_referenceAngular_interval_of_continuous continuous_const
    have he : (fun θ => U.1 (r, θ)) =
        (fun θ => outputRemainder D aL U (r, θ) + aL * D.chiLeft r) := by
      funext θ
      dsimp only [outputRemainder]
      ring
    intro θ
    change angularBasisProjection I (fun α => outputRemainder D aL U (r, α)) θ =
      angularBasisProjection I (fun α => U.1 (r, α)) θ -
        (if 0 ∈ I then aL else 0) * D.chiLeft r
    rw [he, angularBasisProjection_add hr hc I, n07a_angularBasisProjection_const]
    by_cases h0 : 0 ∈ I <;> simp only [h0, ite_true, ite_false] <;> ring
  rw [radialPhysicalMeasure_eq_prod]
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (radialCore D))
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae hs] with x hx
  exact hx x.2

theorem n07a_referenceBasisProjection_outputRealization {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M aL : ℝ}
    {U : RadialUnknown} (hU : OutputRealization D γ M aL U) (I : Finset ℕ) (μ : ℝ) :
    OutputRealization D γ M (if 0 ∈ I then aL else 0)
      (referenceBasisProjection I U.1, μ) := by
  have hp := referenceBasisProjection_cellIntegrable hU.1 I
  have he := n07a_referenceBasisProjection_remainder_ae hpart hU I μ
  have hs : Summable (outputCellSquare D γ M
      (referenceBasisProjection I (outputRemainder D aL U))) := by
    apply hU.2.1.of_nonneg_of_le
      (fun m => mul_nonneg (Real.exp_pos _).le (referenceCellSquare_nonneg hab m hp))
    intro m
    exact mul_le_mul_of_nonneg_left (referenceBasisProjection_cell_sq_le hab hU.1 I m)
      (Real.exp_pos _).le
  refine ⟨hp.congr_ae he, ?_, referenceBasisProjection_periodic I U.1,
    referenceBasisProjection_even I U.1⟩
  apply hs.congr
  intro m
  exact congrArg
    (fun z : ℝ => Real.exp (-2 * M * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m)) * z)
    (referenceCellSquare_congr_ae hab m hp he)

theorem n07a_referenceBasisProjection_sourceMember {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (I : Finset ℕ) (ν : ℝ) :
    SourceMember D γ M (referenceBasisProjection I F.1, ν) := by
  have hp := referenceBasisProjection_cellIntegrable hF.1 I
  have hs : Summable (sourceCellSquare D γ M (referenceBasisProjection I F.1)) := by
    apply hF.2.1.of_nonneg_of_le
      (fun m => mul_nonneg (Real.exp_pos _).le (referenceCellSquare_nonneg hab m hp))
    intro m
    exact mul_le_mul_of_nonneg_left (referenceBasisProjection_cell_sq_le hab hF.1 I m)
      (Real.exp_pos _).le
  refine ⟨hp, hs, referenceBasisProjection_periodic I F.1,
    referenceBasisProjection_even I F.1, ?_, ?_⟩
  · by_cases h0 : 0 ∈ I
    · simpa only [n07a_referenceBasisProjection_mean, ite_eq_left h0] using hF.2.2.2.2.1
    · simpa only [n07a_referenceBasisProjection_mean, ite_eq_right h0] using
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume D.a D.b)
  · by_cases h0 : 0 ∈ I
    · simpa only [n07a_referenceBasisProjection_mean, ite_eq_left h0] using hF.2.2.2.2.2
    · simp only [n07a_referenceBasisProjection_mean, ite_eq_right h0, intervalIntegral.integral_zero]

/-- Projection of the actual weak graph onto any finite set of angular modes.
The border scalar and its row belong to physical frequency `2`, indexed by `1`. -/
theorem n07a_referenceGraph_basisProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) (I : Finset ℕ) :
    ReferenceGraph D γ M₀ M₁
      (referenceBasisProjection I U.1, if 1 ∈ I then U.2 else 0)
      (referenceBasisProjection I F.1, if 1 ∈ I then F.2 else 0) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hu := r11b_output_memLp hD hborder hγ hgraph.1
  have hf := r11b_source_memLp hD hγ hgraph.2.1
  have hc := r11b_continuous_memLp (D := D) (reference_column_mode_continuous hgeom hborder)
  refine ⟨?_, n07a_referenceBasisProjection_sourceMember hgeom.2.1.le hgraph.2.1 I _, ?_, ?_⟩
  · obtain ⟨aL, hU⟩ := hgraph.1
    exact ⟨if 0 ∈ I then aL else 0,
      n07a_referenceBasisProjection_outputRealization hgeom.2.1.le hpart hU I _⟩
  · rw [n07a_referenceBasisProjection_row, hgraph.2.2.1]
  · intro ψ hψ
    have hψL := r11b_continuous_memLp (D := D) hψ.1.continuous
    have h := hgraph.2.2.2 _ (referenceBasisProjection_test hψ I)
    have hcEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hc hψL I
    have hfEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hf hψL I
    rw [← referenceBasisProjection_weakPairing hgeom hu hψ I, ← hfEq] at h
    by_cases h1 : 1 ∈ I
    · rw [referenceBasisProjection_column D h1] at hcEq
      rw [← hcEq] at h
      simpa only [ite_eq_left h1] using h
    · have hz : referenceBasisProjection I
          (fun x : PolarPoint => referenceColumn D x.1 * cosineMode 2 x.2) =
          (fun _ => 0) := by
        simpa only [ite_eq_right h1] using n07a_referenceBasisProjection_column I D
      rw [hz] at hcEq
      have hc0 : (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          referenceColumn D r * cosineMode 2 θ * referenceBasisProjection I ψ (r, θ))) = 0 := by
        rw [← hcEq]
        simp only [zero_mul, radialAngularMean, intervalIntegral.integral_zero, mul_zero]
      rw [hc0, mul_zero, add_zero] at h
      simpa only [ite_eq_right h1, zero_mul, add_zero] using h

/-- Uniqueness of the actual physical inverse gives its band commutation,
including the border coefficient and a.e. equality of the physical field. -/
theorem n07a_referenceInverse_basisProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) {F : RadialSource}
    (hF : SourceMember D γ M₀ F) (I : Finset ℕ) :
    RadialRepresentativeEq D
      (G (referenceBasisProjection I F.1, if 1 ∈ I then F.2 else 0))
      (referenceBasisProjection I (G F).1, if 1 ∈ I then (G F).2 else 0) :=
  hG.2.1 _ _ (n07a_referenceGraph_basisProjection hD hborder hγ (hG.1 F hF) I)

end

end ContinuousFlexibility.Radial
