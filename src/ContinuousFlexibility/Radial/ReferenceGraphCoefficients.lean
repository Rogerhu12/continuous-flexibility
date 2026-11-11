import ContinuousFlexibility.Radial.ReferenceCosineJacobi
import ContinuousFlexibility.Radial.ReferenceRadialWeighted

/-!
# Actual one-dimensional equations of the reference graph

Separated compact tests project the frozen distributional equation and
its first normal derivative onto the genuine mean/cosine coefficients.
The weighted estimates are the fiberwise L² contraction already proved
for the actual localized square integrals.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem reference_basis_lift_test {D : ReferenceData} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) (n : ℕ) :
    RadialTest D (fun x : PolarPoint => φ x.1 * referenceAngularBasis n x.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul ((contDiff_referenceAngularBasis n).comp contDiff_snd),
    ?_, tsupport φ, hφc, hφs, ?_⟩
  · intro x
    simp only [Prod.fst_add, Prod.snd_add, add_zero,
      referenceAngularBasis_periodic_two_pi n x.2]
  · intro r hr θ
    have hz : φ r = 0 := by
      by_contra h
      exact hr (subset_tsupport φ (Function.mem_support.mpr h))
    change φ r * referenceAngularBasis n θ = 0
    rw [hz, zero_mul]

theorem radialPDE_reference_basis_lift {w φ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (r θ : ℝ) :
    radialPDE w (fun s α => φ s * referenceAngularBasis n α) r θ =
      radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) w φ r * referenceAngularBasis n θ := by
  simpa only [Finset.sum_singleton] using
    radialPDE_finite_basis_sum hw {n} (fun _ => φ) (fun _ _ => hφ) r θ

theorem radialPartial_reference_basis_lift {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (r θ : ℝ) :
    radialPartial (fun x : PolarPoint => φ x.1 * referenceAngularBasis n x.2) (r, θ) =
      deriv φ r * referenceAngularBasis n θ := by
  have hψ : ContDiff ℝ ∞ (fun x : PolarPoint => φ x.1 * referenceAngularBasis n x.2) :=
    (hφ.comp contDiff_fst).mul ((contDiff_referenceAngularBasis n).comp contDiff_snd)
  exact (hasDerivAt_radial_slice (hψ.differentiable (by simp) (r, θ))).unique
    ((hφ.differentiable (by simp) r).hasDerivAt.mul_const (referenceAngularBasis n θ))

/-- The normalization is already included in the actual coefficient. -/
theorem reference_mean_mul_basis (u : PolarPoint → ℝ) (a : ℝ → ℝ) (n : ℕ) (r : ℝ) :
    radialAngularMean (fun θ => u (r, θ) * (a r * referenceAngularBasis n θ)) =
      referenceRadialCoefficient u n r * a r := by
  have he : (fun θ => u (r, θ) * (a r * referenceAngularBasis n θ)) =
      (fun θ => a r * (u (r, θ) * referenceAngularBasis n θ)) := by
    funext θ
    ring
  rw [he, radialAngularMean_const_mul]
  exact mul_comm _ _

theorem reference_column_basis_pairing (D : ReferenceData) (φ : ℝ → ℝ) (n : ℕ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * (φ r * referenceAngularBasis n θ))) =
        if n = 1 then ∫ r in D.a..D.b, referenceColumn D r * φ r else 0 := by
  have he (r : ℝ) :
      (fun θ => referenceColumn D r * cosineMode 2 θ * (φ r * referenceAngularBasis n θ)) =
        (fun θ => (referenceColumn D r * φ r) *
          (referenceAngularBasis 1 θ * referenceAngularBasis n θ)) := by
    funext θ
    change referenceColumn D r * cosineMode 2 θ * (φ r * referenceAngularBasis n θ) =
      (referenceColumn D r * φ r) * (cosineMode 2 θ * referenceAngularBasis n θ)
    ring
  simp_rw [he, radialAngularMean_const_mul, referenceAngularBasis_pairing]
  by_cases hn : n = 1
  · subst n
    simp only [ite_true, mul_one]
  · simp only [if_neg hn, if_neg (Ne.symm hn), mul_zero, intervalIntegral.integral_zero]

/-- Scalar coefficient equation obtained directly from the actual weak
two-dimensional graph. Index one is the bordered frequency two. -/
theorem referenceGraph_coefficient_equation {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) (n : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, referenceRadialCoefficient U.1 n r *
      radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) +
        U.2 * (if n = 1 then ∫ r in D.a..D.b, referenceColumn D r * φ r else 0) =
      ∫ r in D.a..D.b, referenceRadialCoefficient F.1 n r * φ r := by
  have h := hgraph.2.2.2 _ (reference_basis_lift_test hφ hφc hφs n)
  have he : radialWeakPairing D U.1
      (fun x : PolarPoint => φ x.1 * referenceAngularBasis n x.2) =
        ∫ r in D.a..D.b, referenceRadialCoefficient U.1 n r *
          radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r := by
    unfold radialWeakPairing
    simp_rw [radialPDE_reference_basis_lift hgeom.2.2.1.1 hφ, reference_mean_mul_basis]
  rw [he, reference_column_basis_pairing] at h
  simpa only [reference_mean_mul_basis] using h

/-- Weak normal differentiation commutes with the actual angular
coefficient on every compactly supported radial test. -/
theorem weakNormalDerivative_coefficient {D : ReferenceData} {u d : PolarPoint → ℝ}
    (hd : WeakNormalDerivative D u d) (n : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, referenceRadialCoefficient u n r * deriv φ r) =
      -(∫ r in D.a..D.b, referenceRadialCoefficient d n r * φ r) := by
  have h := hd _ (reference_basis_lift_test hφ hφc hφs n)
  simpa only [radialPartial_reference_basis_lift hφ, reference_mean_mul_basis] using h

theorem referenceRadialCoefficient_source_weighted {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : RadialCellIntegrable D u) (hs : Summable (sourceCellSquare D γ M u)) (n : ℕ) :
    ReferenceRadialWeighted D γ (2 * M) (referenceRadialCoefficient u n) := by
  refine ⟨fun m => referenceRadialCoefficient_memLp_cell hu n m, ?_⟩
  apply hs.of_nonneg_of_le
    (fun m => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun r => sq_nonneg _))
  intro m
  exact mul_le_mul_of_nonneg_left (referenceRadialCoefficient_cell_sq_le hab hu n m)
    (Real.exp_pos _).le

theorem referenceRadialCoefficient_output_weighted_remainder {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (n : ℕ) :
    ReferenceRadialWeighted D γ (-2 * M)
      (referenceRadialCoefficient (outputRemainder D aL U) n) := by
  refine ⟨fun m => referenceRadialCoefficient_memLp_cell hU.1 n m, ?_⟩
  apply hU.2.1.of_nonneg_of_le
    (fun m => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun r => sq_nonneg _))
  intro m
  exact mul_le_mul_of_nonneg_left (referenceRadialCoefficient_cell_sq_le hab hU.1 n m)
    (Real.exp_pos _).le

theorem referenceAngularCoefficient_const (c : ℝ) (n : ℕ) :
    referenceAngularCoefficient (fun _ => c) n = if n = 0 then c else 0 := by
  have hmean : radialAngularMean (referenceAngularBasis n) = if n = 0 then 1 else 0 := by
    simpa only [referenceAngularBasis, one_mul, eq_comm] using referenceAngularBasis_pairing 0 n
  change radialAngularMean (fun θ => c * referenceAngularBasis n θ) = _
  rw [radialAngularMean_const_mul, hmean]
  split_ifs <;> simp only [mul_one, mul_zero]

theorem referenceRadialCoefficient_output_remainder_ae {D : ReferenceData}
    (hpart : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) {n : ℕ} (hn : n ≠ 0) :
    referenceRadialCoefficient (outputRemainder D aL U) n =ᵐ[volume.restrict (radialCore D)]
      referenceRadialCoefficient U.1 n := by
  filter_upwards [hU.1.ae_angular_memLp hpart] with r hr
  have hc : MemLp (fun _ : ℝ => aL * D.chiLeft r) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    memLp_referenceAngular_interval_of_continuous continuous_const
  have he : (fun θ => U.1 (r, θ)) =
      (fun θ => outputRemainder D aL U (r, θ) + aL * D.chiLeft r) := by
    funext θ
    dsimp only [outputRemainder]
    ring
  change referenceAngularCoefficient (fun θ => outputRemainder D aL U (r, θ)) n =
    referenceAngularCoefficient (fun θ => U.1 (r, θ)) n
  rw [he, referenceAngularCoefficient_add hr hc, referenceAngularCoefficient_const,
    if_neg hn, add_zero]

/-- Every positive angular coefficient of an output has its full weighted
norm; its zero-mode left constant does not enter this estimate. -/
theorem referenceRadialCoefficient_output_weighted {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M aL : ℝ}
    {U : RadialUnknown} (hU : OutputRealization D γ M aL U) {n : ℕ} (hn : n ≠ 0) :
    ReferenceRadialWeighted D γ (-2 * M) (referenceRadialCoefficient U.1 n) :=
  (referenceRadialCoefficient_output_weighted_remainder hab hU n).congr_ae
    (referenceRadialCoefficient_output_remainder_ae hpart hU hn)

theorem referenceRadialCoefficient_output_zero_weighted {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : OutputRealization D γ M 0 (u, 0)) (n : ℕ) :
    ReferenceRadialWeighted D γ (-2 * M) (referenceRadialCoefficient u n) := by
  have h := referenceRadialCoefficient_output_weighted_remainder hab hu n
  have he : outputRemainder D 0 (u, 0) = u := by
    funext x
    simp only [outputRemainder, zero_mul, sub_zero]
  rw [he] at h
  exact h

end

end ContinuousFlexibility.Radial
