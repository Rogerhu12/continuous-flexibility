import ContinuousFlexibility.Radial.InnerGapDirichletSupport
import ContinuousFlexibility.Radial.InnerGapPoissonL2
import ContinuousFlexibility.Radial.InnerWeightL2

/-!
# Exact cancellation of the weights on a positive gap

The inner weight is constant on each entire gap. Actual multiplication
therefore acts as one scalar on every supported gap field. The same
Dirichlet inverse commutes with this multiplication, and the weighted
Poisson map cancels the scalar boundary weight exactly. These identities
apply to either sign and incur no loss depending on the gap or cut count.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerWeightMultiplier_eq_smul_of_support {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) {s : Set α} {c : ℝ}
    (hconstant : EqOn W (fun _ => c) s) (u : Lp ℝ 2 μ)
    (hsupport : ∀ᵐ x ∂μ, x ∉ s → u x = 0) :
    innerWeightMultiplier μ W hW C hbound u = c • u := by
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ W hW C hbound u,
    Lp.coeFn_smul c u, hsupport] with x hM hsmul hs
  rw [hM, hsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ s
  · rw [hconstant hx]
  · rw [hs hx, mul_zero, mul_zero]

section GapWeight

variable (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
  {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
  (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
  (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)

/-- Weighting an arbitrary source before applying the same gap inverse
only multiplies the output by the constant value of the weight on that
gap. Values of the source outside the gap do not affect this identity. -/
theorem innerGapDirichletInverse_multiplier_right (W : ℝ → ℝ)
    (hW : Measurable W) (C : ℝ) (hbound : ∀ r, |W r| ≤ C)
    (c : ℝ) (hconstant : EqOn W (fun _ => c) (Ioo a b)) (F : RadialModeL2 D) :
    innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope
        (innerWeightMultiplier (radialHilbertMeasure D) W hW C hbound F) =
      c • innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope F := by
  let G := innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope
  let M := innerWeightMultiplier (radialHilbertMeasure D) W hW C hbound
  apply (innerGapDirichletInverse_graph_iff D hw hab ha hj hs hcore hpos hslope
    (c • G F) (M F)).mp
  obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b (G F) F).mp
    (innerGapDirichletInverse_graph D hw hab ha hj hs hcore hpos hslope F)
  apply (innerGapFormGraph_iff D j a b (c • G F) (M F)).mpr
  refine ⟨c • q, (innerGapFormSpace D j a b).smul_mem c hq, ?_, ?_⟩
  · simpa only [WithLp.smul_fst] using congrArg (fun u : RadialModeL2 D => c • u) hvalue
  · intro r hr
    have hMr : M r.fst = c • r.fst :=
      innerWeightMultiplier_eq_smul_of_support (radialHilbertMeasure D) W hW C hbound
        hconstant r.fst (innerGapFormSpace_support D j a b r hr)
    have hMadj : M.adjoint = M := innerWeightMultiplier_adjoint
      (radialHilbertMeasure D) W hW C hbound
    have hpair := M.adjoint_inner_left r.fst F
    rw [hMadj, hMr, real_inner_smul_right] at hpair
    calc
      ⟪M F, r.fst⟫_ℝ = c * ⟪F, r.fst⟫_ℝ := hpair
      _ = c * ⟪q.snd, r.snd⟫_ℝ := congrArg (fun z : ℝ => c * z) (hform r hr)
      _ = ⟪(c • q).snd, r.snd⟫_ℝ := by rw [WithLp.smul_snd, real_inner_smul_left]

/-- Any two actual bounded weights whose gap constants are reciprocal
cancel around the constructed Dirichlet inverse. This single identity
applies to both choices of sign. -/
theorem innerGapDirichletInverse_multiplier_conjugate (W V : ℝ → ℝ)
    (hW : Measurable W) (hV : Measurable V) (C B : ℝ)
    (hWC : ∀ r, |W r| ≤ C) (hVB : ∀ r, |V r| ≤ B)
    (c d : ℝ) (hWc : EqOn W (fun _ => c) (Ioo a b))
    (hVd : EqOn V (fun _ => d) (Ioo a b)) (hcd : d * c = 1) :
    innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC ∘L
        innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope ∘L
        innerWeightMultiplier (radialHilbertMeasure D) V hV B hVB =
      innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope := by
  apply ContinuousLinearMap.ext
  intro F
  simp only [ContinuousLinearMap.comp_apply]
  rw [innerGapDirichletInverse_multiplier_right D hw hab ha hj hs hcore hpos hslope
    V hV B hVB d hVd, map_smul,
    innerWeightMultiplier_eq_smul_of_support (radialHilbertMeasure D) W hW C hWC hWc
      _ (innerGapDirichletInverse_support D hw hab ha hj hs hcore hpos hslope F),
    smul_smul, hcd, one_smul]

theorem norm_innerGapDirichletInverse_weighted_le (W V : ℝ → ℝ)
    (hW : Measurable W) (hV : Measurable V) (C B : ℝ)
    (hWC : ∀ r, |W r| ≤ C) (hVB : ∀ r, |V r| ≤ B)
    (c d : ℝ) (hWc : EqOn W (fun _ => c) (Ioo a b))
    (hVd : EqOn V (fun _ => d) (Ioo a b)) (hcd : d * c = 1) :
    ‖innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC ∘L
        innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope ∘L
        innerWeightMultiplier (radialHilbertMeasure D) V hV B hVB‖ ≤
      12 / (s * j ^ 2) := by
  rw [innerGapDirichletInverse_multiplier_conjugate D hw hab ha hj hs hcore hpos hslope
    W V hW hV C B hWC hVB c d hWc hVd hcd]
  exact innerGapDirichletInverse_norm_le D hw hab ha hj hs hcore hpos hslope

end GapWeight

/-- Multiplication by the actual constant gap weight exactly cancels the
reciprocal boundary weight in the very same physical Poisson map. -/
theorem innerGapPoissonL2_multiplier_cancel (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (W : ℝ → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ r, |W r| ≤ C)
    (c : ℝ) (hc : c ≠ 0) (hWc : EqOn W (fun _ => c) (Ioo a b))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC
      (innerGapPoissonL2 D hw ha hcore hpos p hp (c⁻¹ • ξ)) =
        innerGapPoissonL2 D hw ha hcore hpos p hp ξ := by
  rw [map_smul, map_smul,
    innerWeightMultiplier_eq_smul_of_support (radialHilbertMeasure D) W hW C hWC hWc
      _ (innerGapPoissonL2_support D hw ha hcore hpos p hp ξ),
    smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem innerGapPoissonL2_weighted_norm_le (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (W : ℝ → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ r, |W r| ≤ C)
    (c : ℝ) (hc : c ≠ 0) (hWc : EqOn W (fun _ => c) (Ioo a b))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC
      (innerGapPoissonL2 D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp (c⁻¹ • ξ))‖ ≤
      (Real.sqrt (12 / s) / j) * Real.sqrt ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ := by
  rw [innerGapPoissonL2_multiplier_cancel D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp W hW C hWC c hc hWc]
  exact innerGapPoissonL2_norm_le D hw hab ha hj hs hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp hb heq hpos hslope ξ

end ContinuousFlexibility.Radial
