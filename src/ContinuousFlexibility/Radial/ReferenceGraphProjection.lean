module

public import ContinuousFlexibility.Radial.ReferenceGraphCoefficients
public import ContinuousFlexibility.Radial.ReferenceGraphClosed

/-!
# Finite angular projection preserves the actual weak graph

The projection is self-adjoint for the genuine angular integral and
commutes with the actual differential expression on tests. Its zero mode
preserves the left constant and its first positive mode preserves the
border row and column. Uniqueness of the already constructed inverse then
forces finite angular spectrum for finite-mode sources.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem angularBasisProjection_add {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (I : Finset ℕ) :
    angularBasisProjection I (fun θ => f θ + g θ) =
      (fun θ => angularBasisProjection I f θ + angularBasisProjection I g θ) := by
  funext θ
  simp only [angularBasisProjection, referenceAngularCoefficient_add hf hg,
    add_mul, Finset.sum_add_distrib]

theorem angularBasisProjection_const {I : Finset ℕ} (h0 : 0 ∈ I) (c : ℝ) :
    angularBasisProjection I (fun _ => c) = fun _ => c := by
  funext θ
  unfold angularBasisProjection
  rw [Finset.sum_eq_single 0]
  · simp only [referenceAngularCoefficient_const, ite_true, referenceAngularBasis, mul_one]
  · intro n _hn hn0
    rw [referenceAngularCoefficient_const, if_neg hn0, zero_mul]
  · exact fun hn => (hn h0).elim

theorem referenceBasisProjection_remainder_ae {D : ReferenceData}
    (hpart : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) {I : Finset ℕ} (h0 : 0 ∈ I) :
    referenceBasisProjection I (outputRemainder D aL U) =ᵐ[radialPhysicalMeasure D]
      outputRemainder D aL (referenceBasisProjection I U.1, U.2) := by
  have hs : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ θ,
      referenceBasisProjection I (outputRemainder D aL U) (r, θ) =
        outputRemainder D aL (referenceBasisProjection I U.1, U.2) (r, θ) := by
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
      angularBasisProjection I (fun α => U.1 (r, α)) θ - aL * D.chiLeft r
    rw [he, angularBasisProjection_add hr hc I, angularBasisProjection_const h0]
    ring
  rw [radialPhysicalMeasure_eq_prod]
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (radialCore D))
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae hs] with x hx
  exact hx x.2

theorem referenceBasisProjection_outputRealization {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M aL : ℝ}
    {U : RadialUnknown} (hU : OutputRealization D γ M aL U)
    {I : Finset ℕ} (h0 : 0 ∈ I) :
    OutputRealization D γ M aL (referenceBasisProjection I U.1, U.2) := by
  have hp := referenceBasisProjection_cellIntegrable hU.1 I
  have he := referenceBasisProjection_remainder_ae hpart hU h0
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

theorem referenceBasisProjection_lift (I : Finset ℕ) {n : ℕ} (hn : n ∈ I)
    (a : ℝ → ℝ) :
    referenceBasisProjection I (fun x : PolarPoint => a x.1 * referenceAngularBasis n x.2) =
      (fun x : PolarPoint => a x.1 * referenceAngularBasis n x.2) := by
  funext x
  have h := congrFun (angularBasisProjection_sum_basis I {n}
    (Finset.singleton_subset_iff.mpr hn) (fun _ => a x.1)) x.2
  simpa only [Finset.sum_singleton, referenceBasisProjection] using h

theorem referenceBasisProjection_column (D : ReferenceData) {I : Finset ℕ} (h1 : 1 ∈ I) :
    referenceBasisProjection I
      (fun x : PolarPoint => referenceColumn D x.1 * cosineMode 2 x.2) =
        (fun x : PolarPoint => referenceColumn D x.1 * cosineMode 2 x.2) :=
  referenceBasisProjection_lift I h1 (referenceColumn D)

theorem referenceBasisProjection_row (D : ReferenceData) {I : Finset ℕ} (h1 : 1 ∈ I)
    (u : PolarPoint → ℝ) :
    referenceRow D (referenceBasisProjection I u) = referenceRow D u := by
  have he : referenceMode (referenceBasisProjection I u) 2 = referenceMode u 2 := by
    funext r
    change referenceAngularCoefficient (angularBasisProjection I (fun θ => u (r, θ))) 1 =
      referenceAngularCoefficient (fun θ => u (r, θ)) 1
    rw [referenceAngularCoefficient_projection, if_pos h1]
  unfold referenceRow
  rw [he]

/-- Self-adjointness at the level of the actual iterated scalar integral. -/
theorem referenceBasisProjection_integral_pairing {D : ReferenceData} (hab : D.a ≤ D.b)
    {u v : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D)) (I : Finset ℕ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceBasisProjection I u (r, θ) * v (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          u (r, θ) * referenceBasisProjection I v (r, θ)) := by
  have hup : MemLp u 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu
  have hvp : MemLp v 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hv
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [memLp_two_prod_sections hup, memLp_two_prod_sections hvp] with r hru hrv
  exact angularBasisProjection_pairing_symm hru hrv I

theorem referenceBasisProjection_weakPairing {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D)) {ψ : PolarPoint → ℝ}
    (hψ : RadialTest D ψ) (I : Finset ℕ) :
    radialWeakPairing D (referenceBasisProjection I u) ψ =
      radialWeakPairing D u (referenceBasisProjection I ψ) := by
  have hLψ : MemLp
      (fun x : PolarPoint => radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2)
      2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_continuous_radialPDE_test hgeom hψ.1)
  have h := referenceBasisProjection_integral_pairing hgeom.2.1.le hu hLψ I
  rw [referenceBasisProjection_radialPDE hgeom.2.2.1.1 hψ.1 hψ.2.1] at h
  exact h

/-- The projection preserves the given graph, including its unmodified
source and border data, whenever it fixes that source. -/
theorem referenceGraph_basisProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) {I : Finset ℕ}
    (h0 : 0 ∈ I) (h1 : 1 ∈ I) (hF : referenceBasisProjection I F.1 = F.1) :
    ReferenceGraph D γ M₀ M₁ (referenceBasisProjection I U.1, U.2) F := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hu := r11b_output_memLp hD hborder hγ hgraph.1
  have hf := r11b_source_memLp hD hγ hgraph.2.1
  have hc := r11b_continuous_memLp (D := D) (reference_column_mode_continuous hgeom hborder)
  refine ⟨?_, hgraph.2.1, (referenceBasisProjection_row D h1 U.1).trans hgraph.2.2.1, ?_⟩
  · obtain ⟨aL, hU⟩ := hgraph.1
    exact ⟨aL, referenceBasisProjection_outputRealization hgeom.2.1.le hpart hU h0⟩
  · intro ψ hψ
    have hψL := r11b_continuous_memLp (D := D) hψ.1.continuous
    have h := hgraph.2.2.2 _ (referenceBasisProjection_test hψ I)
    have hcEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hc hψL I
    rw [referenceBasisProjection_column D h1] at hcEq
    have hfEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hf hψL I
    rw [hF] at hfEq
    rw [← referenceBasisProjection_weakPairing hgeom hu hψ I, ← hcEq, ← hfEq] at h
    exact h

/-- Actual inverse uniqueness forces finite angular spectrum. -/
theorem referenceGraph_eq_basisProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) {I : Finset ℕ}
    (h0 : 0 ∈ I) (h1 : 1 ∈ I) (hF : referenceBasisProjection I F.1 = F.1) :
    U.1 =ᵐ[radialPhysicalMeasure D] referenceBasisProjection I U.1 :=
  (hG.2.1 U F hgraph).2.symm.trans
    (hG.2.1 _ F (referenceGraph_basisProjection hD hborder hγ hgraph h0 h1 hF)).2

end

end ContinuousFlexibility.Radial
