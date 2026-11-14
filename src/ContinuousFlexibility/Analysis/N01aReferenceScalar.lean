module

public import ContinuousFlexibility.Analysis.N01aReferenceCutoff
public import ContinuousFlexibility.Analysis.N01aReferencePairing

/-!
# Vanishing of the inverse scalar at a pure row

The scalar coefficient is recovered by testing against interior cutoffs of
the actual normalized natural eigenfunction.  The smooth-core approximation
then transfers this conclusion to the reference inverse itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem SourceMember.congr_fst {D : ReferenceData} {γ M : ℝ}
    {F K : RadialSource} (hF : SourceMember D γ M F) (h : K.1 = F.1) :
    SourceMember D γ M K := by
  simpa only [SourceMember, h] using hF

theorem SourceMember.sub_pure_row {D : ReferenceData} {γ M : ℝ}
    {F : RadialSource} (hF : SourceMember D γ M F) (η : ℝ) :
    SourceMember D γ M (F - ((0 : PolarPoint → ℝ), η)) := by
  apply hF.congr_fst
  funext p
  simp only [Prod.fst_sub, Pi.sub_apply, Pi.zero_apply, sub_zero]

/-- The same bound works for every row scalar, because changing the scalar
row does not change the physical forcing in the distributional equation. -/
theorem exists_smooth_reference_scalar_bound {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hkernel : RadialNaturalKernels D) (hborder : RadialTrueBorder D)
    {γ : ℝ} (hγ : 0 < γ) (M₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (M₁ : ℝ) (U : RadialUnknown) (F : RadialSource),
      ReferenceGraph D γ M₀ M₁ U F → SmoothAdmissibleField D U → ∀ η : ℝ,
      |U.2| ≤ K * Real.sqrt
        (sourceNormSquare D γ M₀ (F - ((0 : PolarPoint → ℝ), η))) := by
  obtain ⟨C, hC, hbound⟩ := exists_source_pairing_bound hgeo.2.1.le hpart hγ M₀
  obtain ⟨B, hB, hphi⟩ := hgeo.2.2.2.1.exists_bound
  let K : ℝ := C * (B * Real.sqrt 2)
  have hK : 0 < K := mul_pos hC (mul_pos hB (Real.sqrt_pos.mpr (by norm_num)))
  refine ⟨K, hK, fun M₁ U F hgraph hU η => ?_⟩
  have heq (n : ℕ) :
      radialWeakPairing D U.1 (referencePhiCosineCutoff D n) + U.2 *
          (∫ r in D.a..D.b, referenceColumn D r * referencePhiCutoff D n r) =
        ∫ r in D.a..D.b,
          radialAngularMean (fun θ => F.1 (r, θ) * referencePhiCosineCutoff D n (r, θ)) := by
    have h := hgraph.2.2.2 (referencePhiCosineCutoff D n)
      (radialTest_referencePhiCosineCutoff hgeo.2.2.2.1.1 n)
    change radialWeakPairing D U.1 (referencePhiCosineCutoff D n) + U.2 *
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * Radial.cosineMode 2 θ *
          (referencePhiCutoff D n r * Radial.cosineMode 2 θ))) = _ at h
    rw [referenceColumn_cosine_test] at h
    exact h
  have hlim : Tendsto (fun n =>
      |radialWeakPairing D U.1 (referencePhiCosineCutoff D n) + U.2 *
        (∫ r in D.a..D.b, referenceColumn D r * referencePhiCutoff D n r)|)
      atTop (𝓝 |U.2|) := by
    simpa only [zero_add, mul_one] using
      ((tendsto_radialWeakPairing_referencePhiCutoff hgeo hkernel hU).add
        ((tendsto_referenceColumn_referencePhiCutoff hgeo hborder).const_mul U.2)).abs
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  rw [heq]
  simpa only [Prod.fst_sub, Pi.sub_apply, Pi.zero_apply, sub_zero, K] using
    hbound (F - ((0 : PolarPoint → ℝ), η)) (hgraph.2.1.sub_pure_row η)
      (referencePhiCosineCutoff D n) (B * Real.sqrt 2) (by positivity)
      (abs_referencePhiCosineCutoff_le hphi n)

/-- Smooth-core closure forces the scalar coefficient of every pure-row
solution to vanish; no weighted membership of the eigenfunction is assumed. -/
theorem referenceGraph_pure_row_scalar_eq_zero {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hkernel : RadialNaturalKernels D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown} {η : ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((0 : PolarPoint → ℝ), η)) : U.2 = 0 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_smooth_reference_scalar_bound hgeo hpart hkernel hborder hγ M₀
  obtain ⟨Un, Fn, an, hn, hF, hU⟩ := hcore U ((0 : PolarPoint → ℝ), η) hgraph
  have hscalar0 : Tendsto (fun n => (Un n).2) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simp only [Function.comp_def]
    apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg ((Un n).2))
      (Eventually.of_forall fun n => hbound M₁ (Un n) (Fn n) (hn n).1 (hn n).2.1 η)
    simpa only [Real.sqrt_zero, mul_zero] using hF.sqrt.const_mul K
  have hdiff : Tendsto (fun n => (Un n).2 - U.2) atTop (𝓝 0) := by
    simpa only [Prod.snd_sub] using
      tendsto_output_scalar_of_normSquare hgeo.2.1.le γ M₁
        (fun n => Un n - U) an hU
  have hscalar : Tendsto (fun n => (Un n).2) atTop (𝓝 U.2) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add_const U.2
  exact tendsto_nhds_unique hscalar hscalar0

end ContinuousFlexibility.Statements
