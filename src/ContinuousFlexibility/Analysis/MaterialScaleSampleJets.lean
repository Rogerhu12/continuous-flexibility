module

public import ContinuousFlexibility.Analysis.MaterialScalePhysicalJets
public import ContinuousFlexibility.Analysis.MaterialEndpointWeightTransport
public import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# The actual scale jets at a nearby physical sample

A genuine bounded endpoint-coordinate displacement transfers the pure
physical E0 cost to the same sample. Affine unit rescaling then pays only
a positive power of the physical width. Neither sample nor scale changes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

theorem materialEll_signed_sample_physical_jet_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (inverse : Bool) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (endpointDistance D r) -
        endpointX 1 (endpointDistance D s)| ≤ L →
      |iteratedDeriv n (fun t => if inverse then (T.ell t)⁻¹ else T.ell t) r| ≤
        B * T.E0 s ^ A := by
  obtain ⟨B, A, hB, hA, hphysical⟩ := materialEll_signed_physical_jet_bound hT inverse n
  obtain ⟨K, P, hK, hP, htransfer⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hD (0 : ℝ) (0 : ℝ) hA hL
  refine ⟨B * K, P, mul_nonneg hB hK.le, hP, ?_⟩
  intro r s hr hs hdist
  have hshift : T.E0 r ^ A ≤ K * T.E0 s ^ P := by
    simpa only [Real.rpow_zero, one_mul] using htransfer r s hr hs hdist
  exact (hphysical r hr).trans
    ((mul_le_mul_of_nonneg_left hshift hB).trans_eq (by ring))

/-- The same constants precede every affine interval, physical sample,
unit point and angular order; positive angular derivatives vanish. -/
theorem materialEll_signed_affine_unit_jet_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (inverse : Bool) (a : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ d c s : ℝ,
      |c| ≤ |D.b - D.a| → s ∈ Ioo D.a D.b → ∀ p : PolarPoint,
      d + c * p.1 ∈ Ioo D.a D.b →
      |endpointX 1 (endpointDistance D (d + c * p.1)) -
        endpointX 1 (endpointDistance D s)| ≤ L → ∀ b : ℕ,
      |mixedDerivative a b
        (fun q => if inverse then (T.ell (d + c * q.1))⁻¹ else T.ell (d + c * q.1)) p| ≤
        B * T.E0 s ^ A := by
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    materialEll_signed_sample_physical_jet_bound hT hD inverse a hL
  refine ⟨|D.b - D.a| ^ a * B, A,
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, hA, ?_⟩
  intro d c s hwidth hs p hr hdist b
  let f : ℝ → ℝ := fun t => if inverse then (T.ell t)⁻¹ else T.ell t
  change |mixedDerivative a b (fun q => f (d + c * q.1)) p| ≤ _
  rw [n08_mixedDerivative_radial (fun r => f (d + c * r))]
  have hEs : 0 < T.E0 s := (hT.2.1 s hs).2.2.1
  by_cases hb : b = 0
  · rw [if_pos hb, n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
    have hpow : |c| ^ a ≤ |D.b - D.a| ^ a :=
      pow_le_pow_left₀ (abs_nonneg _) hwidth a
    calc
      _ ≤ |c| ^ a * (B * T.E0 s ^ A) :=
        mul_le_mul_of_nonneg_left (hphysical (d + c * p.1) s hr hs hdist)
          (pow_nonneg (abs_nonneg _) _)
      _ ≤ |D.b - D.a| ^ a * (B * T.E0 s ^ A) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hB (Real.rpow_nonneg hEs.le _))
      _ = _ := by ring
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hB)
      (Real.rpow_nonneg hEs.le _)

end ContinuousFlexibility.Statements
