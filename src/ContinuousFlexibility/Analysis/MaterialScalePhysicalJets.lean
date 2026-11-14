import ContinuousFlexibility.Analysis.MaterialScalarPowerJets
import ContinuousFlexibility.Analysis.SpacesTraceGeometry
import ContinuousFlexibility.Scalar.WeightedMaterialScale

/-!
# Physical jets of the actual material scale and its reciprocal

The given positive logarithmic material jets control every real power of
the actual scale. Its global upper bound and the inverse bound forced by
the first radial expansion then give pure E0 costs for both scale atoms.
No lower floor on the original E0 is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

/-- Physical derivatives retain the true power of the material scale. -/
theorem materialEll_rpow_physical_jet_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n (fun t => T.ell t ^ γ) r| ≤
        B * T.ell r ^ γ * T.E0 r ^ A := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlog, _⟩ := hdata
  apply materialWeight_rpow_physical_jet_bound_of_log_jets hT
    (hT.1 T.ell (by simp)) (fun r hr => (hT.2.1 r hr).1)
  intro k hk
  obtain ⟨C, hC, hb⟩ := hlog k hk
  exact ⟨C, hC, fun r hr => (hb r hr).2.2⟩

/-- One scalar estimate covers the scale and inverse-scale atoms at all
physical derivative orders, with constants before the physical point. -/
theorem materialEll_signed_physical_jet_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (inverse : Bool) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n (fun t => if inverse then (T.ell t)⁻¹ else T.ell t) r| ≤
        B * T.E0 r ^ A := by
  let γ : ℝ := if inverse then -1 else 1
  have hvalue : ∃ C A0 : ℝ, 0 ≤ C ∧ 0 ≤ A0 ∧ ∀ r ∈ Ioo D.a D.b,
      T.ell r ^ γ ≤ C * T.E0 r ^ A0 := by
    cases inverse with
    | false =>
      obtain ⟨L, hL, hLb⟩ := spaces_material_ell_bounded hT
      refine ⟨L, 0, zero_le_one.trans hL, le_rfl, fun r hr => ?_⟩
      simpa [γ] using hLb r hr
    | true =>
      obtain ⟨C, A0, hC, hA0, hb⟩ := materialEll_inv_le_E0 hT
      refine ⟨C, A0, hC, hA0, fun r hr => ?_⟩
      simpa [γ, Real.rpow_neg_one] using hb r hr
  obtain ⟨C, A0, hC, hA0, hvalue⟩ := hvalue
  obtain ⟨B, A, hB, hA, hjets⟩ := materialEll_rpow_physical_jet_bound hT γ n
  have hfunction :
      (fun t => if inverse then (T.ell t)⁻¹ else T.ell t) =
        (fun t => T.ell t ^ γ) := by
    cases inverse <;> funext t <;> simp [γ, Real.rpow_neg_one]
  refine ⟨B * C, A0 + A, mul_nonneg hB hC, add_nonneg hA0 hA, fun r hr => ?_⟩
  rw [hfunction]
  have hE : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  calc
    _ ≤ B * T.ell r ^ γ * T.E0 r ^ A := hjets r hr
    _ ≤ B * (C * T.E0 r ^ A0) * T.E0 r ^ A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hvalue r hr) hB)
        (Real.rpow_nonneg hE.le A)
    _ = (B * C) * T.E0 r ^ (A0 + A) := by
      rw [Real.rpow_add hE]
      ring

end ContinuousFlexibility.Statements
