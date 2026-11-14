module

public import ContinuousFlexibility.Radial.ReferenceRadialWeighted
public import ContinuousFlexibility.Radial.MorseChainScales
public import ContinuousFlexibility.Analysis.WeightedEndpointTrace

/-!
# From scalar reference weights to genuine flat endpoints

The actual lower cell-distance bound controls reciprocal endpoint distance
by a fixed coefficient power. Strict attenuation absorbs that power.
Consequently a positive weighted L² norm supplies the integral hypotheses
of the endpoint-trace theorem. This applies at every derivative order and
does not prescribe endpoint values.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem reference_inverse_distance_coefficient_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {c : ℝ} (hc : c = D.a ∨ c = D.b) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      |(r - c)⁻¹| ≤ C * exp (2 * radialQ (D.cellIndex m)) := by
  obtain ⟨C₀, hgeom, hpart, hC₀, _, _, _, hdist, _⟩ := hD
  refine ⟨C₀ 0 * exp 2, mul_pos (hC₀ 0) (exp_pos _), fun m r hr => ?_⟩
  have hrI := hpart.2.2.2.1 m hr
  have hdpos : 0 < |r - c| := by
    rcases hc with rfl | rfl
    · rw [abs_of_pos (sub_pos.mpr hrI.1)]
      exact sub_pos.mpr hrI.1
    · rw [abs_of_neg (sub_neg.mpr hrI.2)]
      linarith [hrI.2]
  have hlower : (C₀ 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤ |r - c| := by
    apply (hdist m r hr).1.trans
    rcases hc with rfl | rfl
    · rw [abs_of_pos (sub_pos.mpr hrI.1)]
      exact min_le_left _ _
    · rw [abs_of_neg (sub_neg.mpr hrI.2)]
      simpa only [neg_sub] using min_le_right (r - D.a) (D.b - r)
  have hpow : ((D.cellIndex m : ℝ) + 1) ^ 2 ≤
      2 * radialQ (D.cellIndex m) + 2 := by
    nlinarith only [radial_nat_sq_le_Q (D.cellIndex m),
      sq_nonneg ((D.cellIndex m : ℝ) - 1)]
  calc
    |(r - c)⁻¹| = |r - c|⁻¹ := abs_inv _
    _ ≤ ((C₀ 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (mul_pos (inv_pos.mpr (hC₀ 0)) (exp_pos _)) hlower
    _ = C₀ 0 * exp (((D.cellIndex m : ℝ) + 1) ^ 2) := by
      rw [mul_inv_rev, ← exp_neg, neg_neg, inv_inv, mul_comm]
    _ ≤ C₀ 0 * exp (2 * radialQ (D.cellIndex m) + 2) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpow) (hC₀ 0).le
    _ = (C₀ 0 * exp 2) * exp (2 * radialQ (D.cellIndex m)) := by
      rw [exp_add]
      ring

theorem ReferenceRadialWeighted.integrable {D : ReferenceData}
    (hpart : RadialPartition D) {γ A : ℝ} (hγ : 0 < γ)
    {u : ℝ → ℝ} (hu : ReferenceRadialWeighted D γ A u) :
    IntegrableOn u (radialCore D) := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  exact (hu.memLp hpart hγ).integrable (by norm_num)

theorem ReferenceRadialWeighted.integrable_div_endpoint {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ A : ℝ} (hγ : 0 < γ)
    {u : ℝ → ℝ} (hu : ReferenceRadialWeighted D γ A u)
    {c : ℝ} (hc : c = D.a ∨ c = D.b) :
    IntegrableOn (fun r => u r / (r - c)) (radialCore D) := by
  obtain ⟨C, hC, hbound⟩ := reference_inverse_distance_coefficient_bound hD hc
  have hp : RadialPartition D := hD.choose_spec.2.1
  have hm : AEStronglyMeasurable (fun r : ℝ => (r - c)⁻¹)
      (volume.restrict (radialCore D)) :=
    ((measurable_id.sub measurable_const).inv).aestronglyMeasurable
  have hw : ReferenceRadialWeighted D (γ / 2) 0 (fun r => (r - c)⁻¹ * u r) :=
    hu.mul_coefficient hp 0 (by linarith : γ / 2 < γ) hm hC.le hbound
  simpa only [div_eq_mul_inv, mul_comm] using hw.integrable hp (by positivity : 0 < γ / 2)

/-- Positive weighted L² membership for every actual derivative suffices
for an actual C∞ zero extension. The exponent may depend on the order. -/
theorem reference_contDiff_zero_extension_of_weighted_jets {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hjets : ∀ s : ℕ, ∃ γ A : ℝ, 0 < γ ∧
      ReferenceRadialWeighted D γ A (iteratedDeriv s u)) :
    ContDiff ℝ ∞ (Analysis.extendZeroOutside D.a D.b u) := by
  have hi (s : ℕ) : IntegrableOn (iteratedDeriv s u) (radialCore D) := by
    obtain ⟨γ, A, hγ, hs⟩ := hjets s
    exact hs.integrable hD.choose_spec.2.1 hγ
  have hd (c : ℝ) (hc : c = D.a ∨ c = D.b) (s : ℕ) :
      IntegrableOn (fun r => iteratedDeriv s u r / (r - c)) (radialCore D) := by
    obtain ⟨γ, A, hγ, hs⟩ := hjets s
    exact hs.integrable_div_endpoint hD hγ hc
  exact Analysis.contDiff_zero_extension_of_integrable_jets hD.choose_spec.1.2.1 hu hi
    (hd D.a (Or.inl rfl)) (hd D.b (Or.inr rfl))

end ContinuousFlexibility.Radial
