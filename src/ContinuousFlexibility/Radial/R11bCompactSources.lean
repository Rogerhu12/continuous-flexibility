module

public import ContinuousFlexibility.Radial.R11bRadialTests
public import ContinuousFlexibility.Statements.RadialTargets

/-!
# Interior corrections in every radial cell weight

A field supported in a compact radial subset of the core meets only finitely
many cells. Continuous corrections therefore belong to every weighted cell
space. The actual matched border has this strict interior support; the same
argument will apply to the derivative of the left-tail cutoff.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_cellSquare_zero_of_disjoint_support {D : ReferenceData}
    (hpart : RadialPartition D) {K : Set ℝ} {f : PolarPoint → ℝ}
    (hzero : ∀ r ∈ radialCore D, r ∉ K → ∀ θ, f (r, θ) = 0)
    {m : ℕ} (hm : ¬(D.cells m ∩ K).Nonempty) :
    referenceCellSquare D m f = 0 := by
  have hz (r θ : ℝ) : D.localizer m r * f (r, θ) = 0 := by
    by_cases hχ : D.localizer m r = 0
    · rw [hχ, zero_mul]
    · have hrm : r ∈ D.cells m := hpart.2.2.1 m hχ
      have hrK : r ∉ K := fun hr => hm ⟨r, hrm, hr⟩
      rw [hzero r (hpart.2.2.2.1 m hrm) hrK θ, mul_zero]
  simp only [referenceCellSquare, radialAngularMean, hz, zero_pow (by decide : 2 ≠ 0),
    intervalIntegral.integral_zero, mul_zero]

/-- No quantitative bound on the number of cells at one index is used. -/
theorem r11b_compact_weighted_cells {D : ReferenceData} (hpart : RadialPartition D)
    {K : Set ℝ} (hfinite : Set.Finite {m : ℕ | (D.cells m ∩ K).Nonempty})
    {f : PolarPoint → ℝ} (hf : Continuous f)
    (hzero : ∀ r ∈ radialCore D, r ∉ K → ∀ θ, f (r, θ) = 0)
    (W : ℕ → ℝ) :
    RadialCellIntegrable D f ∧ Summable (fun m => W m * referenceCellSquare D m f) := by
  refine ⟨fun m => r11b_continuous_memLp
    (((hpart.1 m).continuous.comp continuous_fst).mul hf), ?_⟩
  apply summable_of_hasFiniteSupport
  apply hfinite.subset
  intro m hm
  by_contra hmiss
  have hz := r11b_cellSquare_zero_of_disjoint_support hpart hzero hmiss
  apply hm
  change W m * referenceCellSquare D m f = 0
  rw [hz, mul_zero]

theorem r11b_compact_sourceDerivativeMember {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ} (hK : IsCompact K)
    (hKcore : K ⊆ radialCore D) {f : PolarPoint → ℝ} (hf : Continuous f)
    (hzero : ∀ r ∈ radialCore D, r ∉ K → ∀ θ, f (r, θ) = 0) (γ M : ℝ) :
    SourceDerivativeMember D γ M f := by
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hindex, hfinite, hrest⟩ := hD
  exact r11b_compact_weighted_cells hpart (hfinite K hK hKcore) hf hzero
    (fun m => Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))

theorem r11b_compact_output_cell_summable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ} (hK : IsCompact K)
    (hKcore : K ⊆ radialCore D) {f : PolarPoint → ℝ} (hf : Continuous f)
    (hzero : ∀ r ∈ radialCore D, r ∉ K → ∀ θ, f (r, θ) = 0) (γ M : ℝ) :
    RadialCellIntegrable D f ∧ Summable (outputCellSquare D γ M f) := by
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hindex, hfinite, hrest⟩ := hD
  exact r11b_compact_weighted_cells hpart (hfinite K hK hKcore) hf hzero
    (fun m => Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))

/-- The matching cuts locate the actual border strictly inside the core. -/
theorem r11b_referenceColumn_compact_core {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      Function.support (referenceColumn D) ⊆ K := by
  refine ⟨Icc M.innerLeft M.innerRight, isCompact_Icc, ?_, ?_⟩
  · intro r hr
    exact ⟨hM.1.trans_le hr.1, hr.2.trans_lt hM.2.2.1⟩
  · intro r hr
    exact Ioo_subset_Icc_self (hM.2.2.2.1 hr)

/-- In particular the finite-dimensional border correction has every
source coefficient weight, irrespective of the chosen attenuation. -/
theorem r11b_referenceColumn_sourceDerivativeMember {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M) (γ A : ℝ) (j : ℕ) :
    SourceDerivativeMember D γ A
      (fun x : PolarPoint => referenceColumn D x.1 * cosineMode j x.2) := by
  obtain ⟨K, hK, hKcore, hs⟩ := r11b_referenceColumn_compact_core hM
  obtain ⟨C, hgeom, hrest⟩ := hD
  have hc : Continuous (cosineMode j) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  apply r11b_compact_sourceDerivativeMember ⟨C, hgeom, hrest⟩ hK hKcore
    (((r11b_continuous_referenceColumn hgeom hborder).comp continuous_fst).mul
      (hc.comp continuous_snd))
  intro r hr hrK θ
  have hz : referenceColumn D r = 0 := by
    by_contra hne
    exact hrK (hs hne)
  change referenceColumn D r * cosineMode j θ = 0
  rw [hz, zero_mul]

end ContinuousFlexibility.Radial
