module

public import ContinuousFlexibility.Analysis.N07aAngularRadialWeights
public import ContinuousFlexibility.Radial.R11bCompactSources
public import ContinuousFlexibility.Radial.ReferenceColumnSmooth
public import ContinuousFlexibility.Radial.R11bZeroMode
public import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# The actual physical and radial cutoffs give the same natural output class

The canonical representation subtracts `S.chiLeft`, while the radial graph
subtracts `D.chiLeft`. Their equality is not assumed. Their difference is
supported in a compact subset of the core, by the two actual endpoint
conditions, and therefore belongs to every reference cell weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n07a_cutoffDifference_compact_core {D : ReferenceData} {χ : ℝ → ℝ}
    (hχ : CutoffConditions D χ) (hborder : RadialTrueBorder D) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, r ∉ K → χ r - D.chiLeft r = 0 := by
  obtain ⟨δ₀, hδ₀, _, hχleft, hχright⟩ := hχ.2.1
  obtain ⟨ε, hε, hDleft, hDright⟩ := hborder.2.2.2.2.2
  let δ : ℝ := min (δ₀ / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ₀' : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨Icc (D.a + δ) (D.b - δ), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · intro r hr hrK
    change ¬(D.a + δ ≤ r ∧ r ≤ D.b - δ) at hrK
    rcases not_and_or.mp hrK with hleft | hright
    · rw [hχleft r (by linarith [lt_of_not_ge hleft]),
        hDleft r ⟨hr.1, by linarith [lt_of_not_ge hleft]⟩, sub_self]
    · rw [hχright r (by linarith [lt_of_not_ge hright]),
        hDright r ⟨by linarith [lt_of_not_ge hright], hr.2⟩, sub_self]

theorem n07a_cutoffDifference_output_cells {D : ReferenceData} {χ : ℝ → ℝ}
    (hD : IsAccumulatingProfile D) (hχ : CutoffConditions D χ)
    (hborder : RadialTrueBorder D) (aL γ M : ℝ) :
    RadialCellIntegrable D (fun p : PolarPoint => aL * (χ p.1 - D.chiLeft p.1)) ∧
      Summable (outputCellSquare D γ M
        (fun p : PolarPoint => aL * (χ p.1 - D.chiLeft p.1))) := by
  obtain ⟨K, hK, hKcore, hzero⟩ := n07a_cutoffDifference_compact_core hχ hborder
  apply r11b_compact_output_cell_summable hD hK hKcore
    (continuous_const.mul ((hχ.1.continuous.comp continuous_fst).sub
      (hborder.2.2.2.2.1.continuous.comp continuous_fst)))
  intro r hr hrK θ
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
  rw [hzero r hr hrK, mul_zero]

/-- This changes the actual cutoff in the output remainder. It does not
change the unknown field or its explicit left scalar. -/
theorem n07a_outputRealization_of_physical_cutoff {D : ReferenceData} {χ : ℝ → ℝ}
    (hD : IsAccumulatingProfile D) (hχ : CutoffConditions D χ)
    (hborder : RadialTrueBorder D) {γ M aL μ : ℝ} {η : PolarPoint → ℝ}
    (hcell : RadialCellIntegrable D (fun p => η p - aL * χ p.1))
    (hsum : Summable (outputCellSquare D γ M (fun p => η p - aL * χ p.1)))
    (hperiod : Function.Periodic η (0, Real.pi))
    (heven : ∀ r θ, η (r, -θ) = η (r, θ)) :
    OutputRealization D γ M aL (η, μ) := by
  obtain ⟨hc, hs⟩ := n07a_cutoffDifference_output_cells hD hχ hborder aL γ M
  have heq : outputRemainder D aL (η, μ) =
      (fun p => (η p - aL * χ p.1) + aL * (χ p.1 - D.chiLeft p.1)) := by
    funext p
    dsimp only [outputRemainder]
    ring
  refine ⟨?_, ?_, hperiod, heven⟩
  · rw [heq]
    exact hcell.add hc
  · rw [heq]
    exact outputCellSquare_summable_add hD.choose_spec.1.2.1.le hcell hc hsum hs

/-- Actual material decay enters every requested lower-exponent natural
output space, with its original real coefficient weight. -/
theorem n07a_outputRealization_of_material_decay
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hχ : CutoffConditions D χ) (hborder : RadialTrueBorder D)
    {γ β M aL μ A : ℝ} (hβ : 0 < β) (hγ : γ < β) (q : ℝ)
    {η : PolarPoint → ℝ}
    (hf : AEStronglyMeasurable (fun p => η p - aL * χ p.1) (radialPhysicalMeasure D))
    (hA : 0 ≤ A)
    (hdecay : ∀ p ∈ annularOpen D,
      |η p - aL * χ p.1| ≤ A * T.H p.1 ^ β * T.M p.1 ^ q)
    (hperiod : Function.Periodic η (0, Real.pi))
    (heven : ∀ r θ, η (r, -θ) = η (r, θ)) :
    OutputRealization D γ M aL (η, μ) := by
  let γhi : ℝ := (γ + β) / 2
  have hγlo : γ < γhi := by dsimp only [γhi]; linarith
  have hγhi : γhi < β := by dsimp only [γhi]; linarith
  obtain ⟨hc, _, hs⟩ := n07a_material_decay_reference_cells hD.choose_spec.2.1
    hD.choose_spec.1.2.1.le hT hβ hγhi q hf hA hdecay
  have hnatural : OutputRealization D γhi 0 aL (η, μ) :=
    n07a_outputRealization_of_physical_cutoff hD hχ hborder hc hs hperiod heven
  exact r11b_outputRealization_of_lt hD.choose_spec.1.2.1.le hγlo hnatural

/-- The same attenuation margin supplies the genuine source cell norm.
The last two premises are the actual conserved mean, proved separately by
the reference flux FTC; they are not weighted-space membership premises. -/
theorem n07a_sourceMember_of_material_decay
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ β M A ξ : ℝ} (hβ : 0 < β) (hγ : γ < β) (q : ℝ)
    {f : PolarPoint → ℝ} (hf : AEStronglyMeasurable f (radialPhysicalMeasure D))
    (hA : 0 ≤ A)
    (hdecay : ∀ p ∈ annularOpen D, |f p| ≤ A * T.H p.1 ^ β * T.M p.1 ^ q)
    (hperiod : Function.Periodic f (0, Real.pi))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hint : IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ)))
      volume D.a D.b)
    (hzero : (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) = 0) :
    SourceMember D γ M (f, ξ) := by
  let γhi : ℝ := (γ + β) / 2
  have hγlo : γ < γhi := by dsimp only [γhi]; linarith
  have hγhi : γhi < β := by dsimp only [γhi]; linarith
  obtain ⟨hc, hs, _⟩ := n07a_material_decay_reference_cells hD.choose_spec.2.1
    hD.choose_spec.1.2.1.le hT hβ hγhi q hf hA hdecay
  have hsource : SourceMember D γhi 0 (f, ξ) := ⟨hc, hs, hperiod, heven, hint, hzero⟩
  exact r11b_sourceMember_of_lt hD.choose_spec.1.2.1.le hγlo hsource

/-- The actual border column belongs to every natural source weight.
Its strict interior support follows directly from the real cutoff used
to define it; no modal inverse or matching representation is required. -/
theorem n07a_referenceBorder_sourceMember {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) (γ M : ℝ) :
    SourceMember D γ M ((fun p : PolarPoint =>
      referenceColumn D p.1 * cosineMode 2 p.2), 0) := by
  have hgeom := hD.choose_spec.1
  have hc : Continuous (fun p : PolarPoint => referenceColumn D p.1 * cosineMode 2 p.2) :=
    ((referenceColumn_contDiff hgeom hborder).continuous.comp continuous_fst).mul
      ((r11b_contDiff_cosineMode 2).continuous.comp continuous_snd)
  have hsupport : tsupport (referenceColumn D) ⊆ radialCore D :=
    referenceColumn_tsupport_subset.trans (fun _ hr => (hborder.2.2.1 hr).1)
  obtain ⟨hcell, hsum⟩ := r11b_compact_sourceDerivativeMember hD
    (referenceColumn_hasCompactSupport hborder) hsupport hc
    (fun r _ hr θ => by
      rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]) γ M
  have hmean (r : ℝ) : radialAngularMean
      (fun θ => referenceColumn D r * cosineMode 2 θ) = 0 := by
    rw [radialAngularMean_const_mul, r11b_radialAngularMean_eq_angularAverage,
      angularAverage_cosineMode 2 (by decide), mul_zero]
  refine ⟨hcell, hsum, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    exact congrArg (referenceColumn D p.1 * ·) (cosineMode_even_frequency_periodic 1 p.2)
  · intro r θ
    exact congrArg (referenceColumn D r * ·) (cosineMode_even 2 θ)
  · simpa only [hmean] using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume D.a D.b)
  · simp only [hmean, intervalIntegral.integral_zero]

end ContinuousFlexibility.Analysis
