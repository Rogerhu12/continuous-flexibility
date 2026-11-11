import ContinuousFlexibility.Analysis.N01aReferenceModeIdentification

/-!
# Weighted membership of the actual normalized eigenfield

The second-mode projection of the inverse pays only one fixed L² constant.
Its weighted cell sum is therefore finite at the same spare exponent and
with the same coefficient weight as the given inverse output.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem referenceCellSquare_cosine_lift (D : ReferenceData) (m : ℕ)
    (f : ℝ → ℝ) (j : ℕ) (hj : 0 < j) :
    referenceCellSquare D m (fun p => f p.1 * Radial.cosineMode j p.2) =
      ∫ r in D.a..D.b, (D.localizer m r * f r) ^ 2 := by
  unfold referenceCellSquare
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show (fun θ => (D.localizer m r * (f r * Radial.cosineMode j θ)) ^ 2) =
    (fun θ => (D.localizer m r * f r) ^ 2 *
      (Radial.cosineMode j θ * Radial.cosineMode j θ)) by funext θ; ring]
  rw [radialAngularMean_const_mul, radialAngularMean_cosineMode_product j j hj hj]
  simp only [ite_true, mul_one]

theorem radialCellIntegrable_cosine_lift {D : ReferenceData}
    (hpart : RadialPartition D) {f : ℝ → ℝ} (hf : Continuous f) (j : ℕ) :
    RadialCellIntegrable D (fun p => f p.1 * Radial.cosineMode j p.2) := by
  intro m
  have hl : Continuous (D.localizer m) := (hpart.1 m).continuous
  have hc : Continuous (fun p : PolarPoint =>
      D.localizer m p.1 * (f p.1 * Radial.cosineMode j p.2)) := by
    unfold Radial.cosineMode
    fun_prop
  exact (continuous_memLp_radialPhysicalMeasure hc).integrable_sq

theorem outputRealization_cosine_of_mode_eq {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) (hchi : Continuous D.chiLeft)
    {γ M aL : ℝ} {U : RadialUnknown} {f : ℝ → ℝ}
    (hU : MemLp U.1 2 (radialPhysicalMeasure D))
    (hreal : OutputRealization D γ M aL U) (hf : Continuous f)
    (hmode : referenceMode U.1 2 =ᵐ[volume.restrict (radialCore D)] f) :
    OutputRealization D γ M 0 ((fun p => f p.1 * Radial.cosineMode 2 p.2), 0) := by
  let g : PolarPoint → ℝ := fun p => f p.1 * Radial.cosineMode 2 p.2
  have hremm : AEStronglyMeasurable (outputRemainder D aL U) (radialPhysicalMeasure D) :=
    hU.aestronglyMeasurable.sub
      (continuous_const.mul (hchi.comp continuous_fst)).aestronglyMeasurable
  have hremMode := (referenceMode_outputRemainder_ae hchi hU aL 2 (by decide)).trans hmode
  let K : ℝ := referenceModeL2Constant ^ 2 * (2 * Real.pi)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hcell (m : ℕ) : referenceCellSquare D m g ≤
      K * referenceCellSquare D m (outputRemainder D aL U) := by
    have hm : MemLp (fun p : PolarPoint =>
        D.localizer m p.1 * outputRemainder D aL U p) 2 (radialPhysicalMeasure D) :=
      (memLp_two_iff_integrable_sq
        (((hpart.1 m).continuous.comp continuous_fst).aestronglyMeasurable.mul hremm)).mpr
          (hreal.1.integrable_square m)
    rw [radialPhysicalMeasure_eq_prod] at hm
    have hp := (referenceMode_memLp_two_and_integral_bound hm 2).2
    rw [← radialPhysicalMeasure_eq_prod,
      integral_reference_cell_square hab hreal.1 m] at hp
    have heq : (∫ r, referenceMode (fun p : PolarPoint =>
        D.localizer m p.1 * outputRemainder D aL U p) 2 r ^ 2
        ∂volume.restrict (radialCore D)) =
        ∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D) := by
      apply integral_congr_ae
      filter_upwards [hremMode] with r hr
      dsimp only
      rw [referenceMode_mul_radial, hr]
    rw [heq] at hp
    rw [referenceCellSquare_cosine_lift D m f 2 (by decide),
      intervalIntegral.integral_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    exact hp.trans_eq (by dsimp only [K]; ring)
  have hweighted (m : ℕ) : outputCellSquare D γ M g m ≤
      K * outputCellSquare D γ M (outputRemainder D aL U) m := by
    have h := mul_le_mul_of_nonneg_left (hcell m)
      (Real.exp_pos (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))).le
    simpa only [outputCellSquare, mul_left_comm, mul_assoc] using h
  have hs : Summable (outputCellSquare D γ M g) :=
    Summable.of_nonneg_of_le (fun m => outputCellSquare_nonneg hab γ M g m) hweighted
      (hreal.2.1.mul_left K)
  have hrem : outputRemainder D 0 (g, 0) = g := by
    funext p
    simp only [outputRemainder, zero_mul, sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrem]
    exact radialCellIntegrable_cosine_lift hpart hf 2
  · rw [hrem]
    exact hs
  · intro p
    change f (p.1 + 0) * Radial.cosineMode 2 (p.2 + Real.pi) =
      f p.1 * Radial.cosineMode 2 p.2
    rw [add_zero]
    congr 1
    simpa only [Nat.mul_one] using Radial.cosineMode_even_frequency_periodic 1 p.2
  · intro r θ
    exact congrArg (fun x => f r * x) (Radial.cosineMode_even 2 θ)

theorem referenceGraph_pure_row_eigenfield_output {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hkernel : RadialNaturalKernels D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((0 : PolarPoint → ℝ), 1)) :
    OutputRealization D γ M₁ 0
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0) := by
  have hchi : ContDiff ℝ ∞ D.chiLeft := hborder.2.2.2.2.1
  have hU := hgraph.memLp_two hgeo.2.1.le hpart hchi hγ hcore
  obtain ⟨aL, haL⟩ := hgraph.1
  apply outputRealization_cosine_of_mode_eq hgeo.2.1.le hpart hchi.continuous
    hU haL hgeo.2.2.2.1.1.continuous
  simpa only [one_mul] using
    referenceGraph_pure_row_mode_eq hgeo hpart hkernel hborder hγ hcore hgraph

end ContinuousFlexibility.Statements
