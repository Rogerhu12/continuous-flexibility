import ContinuousFlexibility.Radial.ReferenceZeroModeGraph
import ContinuousFlexibility.Radial.FourierOrthogonality
import ContinuousFlexibility.Radial.MatchedModePhysicalEquation

/-!
# Cosine projection of the actual two-dimensional weak graph

These lemmas use the same normalized angular integrals as ReferenceGraph.
The tests here have topological radial support compactly contained in the
core. Extension to the larger frozen modal test class is a separate step.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem radialTest_cosine_lift {D : ReferenceData} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ radialCore D) (j : ℕ) :
    RadialTest D (fun x => ψ x.1 * Radial.cosineMode j x.2) := by
  have hc : ContDiff ℝ ∞ (Radial.cosineMode j) := by
    unfold Radial.cosineMode
    fun_prop
  refine ⟨(hψ.comp contDiff_fst).mul (hc.comp contDiff_snd), ?_,
    tsupport ψ, hcψ, hψs, ?_⟩
  · intro x
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    unfold Radial.cosineMode
    rw [mul_add, Real.cos_add_nat_mul_two_pi]
  · intro r hr θ
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem radialAngularMean_separated_cosine (f : ℝ → ℝ) (c : ℝ) (j : ℕ) :
    radialAngularMean (fun θ => f θ * (c * Radial.cosineMode j θ)) =
      radialAngularMean (fun θ => f θ * Radial.cosineMode j θ) * c := by
  have he : (fun θ => f θ * (c * Radial.cosineMode j θ)) =
      (fun θ => (f θ * Radial.cosineMode j θ) * c) := by
    funext θ
    ring
  rw [he, radialAngularMean_mul_const]

theorem radialWeakPairing_cosine_lift {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : PolarPoint → ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    radialWeakPairing D u (fun x => ψ x.1 * Radial.cosineMode j x.2) =
      ∫ r in D.a..D.b,
        referenceMode u j r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
  have hw : ContDiff ℝ ∞ D.w := (Radial.matchingProfileGeometry hD).2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hsep (r θ : ℝ) :=
    Radial.radialPDE_cosine_lift (r := r) (θ := θ) j
      (Filter.Eventually.of_forall (fun t => hψ.differentiable (by simp) t))
      ((hw.mul hdψ).differentiable (by simp) r)
  unfold radialWeakPairing
  apply intervalIntegral.integral_congr
  intro r _
  simp only [hsep, radialAngularMean_separated_cosine, referenceMode]

theorem referenceColumn_cosine_lift_mean (D : ReferenceData)
    (ψ : ℝ → ℝ) (r : ℝ) {j : ℕ} (hj : 0 < j) :
    radialAngularMean (fun θ =>
      referenceColumn D r * Radial.cosineMode 2 θ *
        (ψ r * Radial.cosineMode j θ)) =
      if j = 2 then referenceColumn D r * ψ r else 0 := by
  have he : (fun θ => referenceColumn D r * Radial.cosineMode 2 θ *
      (ψ r * Radial.cosineMode j θ)) =
      (fun θ => (referenceColumn D r * ψ r) *
        (Radial.cosineMode 2 θ * Radial.cosineMode j θ)) := by
    funext θ
    ring
  have ho :
      radialAngularMean (fun θ => Radial.cosineMode 2 θ * Radial.cosineMode j θ) =
        if j = 2 then 1 else 0 := by
    simpa only [Radial.angularPairing, Radial.angularAverage, one_div,
      radialAngularMean, eq_comm] using
      Radial.angularPairing_cosineMode 2 j (by norm_num) hj
  rw [he, radialAngularMean_const_mul, ho]
  by_cases hj2 : j = 2 <;> simp only [hj2, ite_true, ite_false, mul_one, mul_zero]

/-- Every positive cosine mode of the actual graph satisfies the physical
Jacobi equation for compactly contained radial tests. -/
theorem ReferenceGraph.modeWeak_compactCore {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) {j : ℕ} (hj : 0 < j)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ radialCore D) :
    (∫ r in D.a..D.b, referenceMode U.1 j r *
      Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
      (if j = 2 then U.2 else 0) *
        (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      ∫ r in D.a..D.b, referenceMode F.1 j r * ψ r := by
  have he := hG.2.2.2 (fun x => ψ x.1 * Radial.cosineMode j x.2)
    (radialTest_cosine_lift hψ hcψ hψs j)
  rw [radialWeakPairing_cosine_lift hD U.1 hψ j] at he
  simp only [radialAngularMean_separated_cosine, referenceColumn_cosine_lift_mean D ψ _ hj,
    ← referenceMode] at he
  by_cases hj2 : j = 2
  · simpa only [hj2, ite_true] using he
  · simpa only [hj2, ite_false, intervalIntegral.integral_zero, mul_zero,
      zero_mul, add_zero] using he

/-- The bordered row is the same actual frequency-two coefficient, also
when its representative is supplied as a modal L² vector. -/
theorem ReferenceGraph.modeTwo_row_of_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) {u : RadialModeL2 D}
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] referenceMode U.1 2) :
    (∫ r in D.a..D.b, referenceColumn D r * u r) = F.2 := by
  calc
    _ = ∫ r in D.a..D.b, referenceColumn D r * referenceMode U.1 2 r := by
      apply Radial.matchingInterval_congr_ae hD
      filter_upwards [hu] with r hr
      rw [hr]
    _ = F.2 := hG.2.2.1

end ContinuousFlexibility.Statements
