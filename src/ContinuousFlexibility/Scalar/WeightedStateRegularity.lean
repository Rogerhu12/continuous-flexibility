import ContinuousFlexibility.Statements.ScalarWeighted
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Scalar.RectangleParameterIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Global regularity of the actual weighted scalar state

The height and profile in this file are precisely the decoded functions in
`Statements.ScalarWeighted`. Their smoothness, support, primitive and endpoint
constants hold for every state, before restricting to the low-order ball used
for the discriminant and denominator estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Decoded scalar heights are globally smooth and flat at both physical ends. -/
theorem scalarHeight_decode_contDiff_and_flatJets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) :
    ContDiff ℝ ∞ ((S.height scalarBeta).decode u) ∧
      UniformFlatJets D ((S.height scalarBeta).decode u) :=
  physical_height_contDiff_and_flatJets hT hS (by norm_num [scalarBeta]) u

/-- The common height domain includes its actual, fixed left cutoff. -/
theorem scalarCommonHeightDecode_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarCommonHeight S) : ContDiff ℝ ∞ (scalarCommonHeightDecode S u) :=
  physical_height_with_cutoff_contDiff hT hS (by norm_num [scalarBeta]) u.1 u.2

theorem scalarStateIncrement_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) : ContDiff ℝ ∞ (scalarStateIncrement S x) :=
  scalarCommonHeightDecode_contDiff hT hS (x.1.1.2, x.1.2)

theorem scalarStateDecodedHeight_uniformFlatJets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    UniformFlatJets D ((S.height scalarBeta).decode x.1.1.2) :=
  (scalarHeight_decode_contDiff_and_flatJets hT hS x.1.1.2).2

/-- Angular averaging preserves the actual global smoothness of a field. -/
theorem contDiff_angularMean_radial {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun r => angularMean (fun θ => f (r, θ))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  exact contDiffAt_const.mul
    (contDiffAt_intervalIntegral_parameter (O := univ) isOpen_univ Real.pi_pos.le
      (fun _ _ _ _ => hf.contDiffAt) (mem_univ r))

/-- The scalar profile is smooth for every state, without a smallness premise. -/
theorem scalarStateProfile_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ContDiff ℝ ∞ (scalarStateProfile D S x) := by
  obtain ⟨C, hC⟩ := hD
  exact hC.1.2.2.1.1.mul (contDiff_const.add
    (contDiff_angularMean_radial
      (scalarHeight_decode_contDiff_and_flatJets hT hS x.1.1.1).1))

/-- The profile support follows directly from the reference profile support. -/
theorem scalarStateProfile_eq_zero_outside
    (hD : IsAccumulatingProfile D) (x : ScalarWeightedState S)
    {r : ℝ} (hr : r ≤ D.a ∨ D.b ≤ r) : scalarStateProfile D S x r = 0 := by
  obtain ⟨C, hC⟩ := hD
  unfold scalarStateProfile
  rw [hC.1.2.2.1.2 r hr, zero_mul]

theorem scalarStateProfile_endpointFlat
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    EndpointFlat D (scalarStateProfile D S x) :=
  ⟨scalarStateProfile_contDiff hD hT hS x,
    fun _ hr => scalarStateProfile_eq_zero_outside hD x hr⟩

/-- Fundamental theorem of calculus for the normalized primitive in the state. -/
theorem scalarStatePrimitive_hasDerivAt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) (r : ℝ) :
    HasDerivAt (scalarStatePrimitive D S x) (scalarStateProfile D S x r) r := by
  have hw := (scalarStateProfile_contDiff hD hT hS x).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable D.a r)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem scalarStatePrimitive_deriv
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    deriv (scalarStatePrimitive D S x) = scalarStateProfile D S x :=
  funext fun r => (scalarStatePrimitive_hasDerivAt hD hT hS x r).deriv

theorem scalarStatePrimitive_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ContDiff ℝ ∞ (scalarStatePrimitive D S x) := by
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun r => (scalarStatePrimitive_hasDerivAt hD hT hS x r).differentiableAt, ?_⟩
  rw [scalarStatePrimitive_deriv hD hT hS x]
  exact scalarStateProfile_contDiff hD hT hS x

theorem scalarStateHeight_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ContDiff ℝ ∞ (scalarStateHeight D S x) :=
  ((scalarStatePrimitive_contDiff hD hT hS x).comp contDiff_fst).add
    (contDiff_const.mul (scalarStateIncrement_contDiff hT hS x))

theorem scalarHeight_decode_eq_zero_outside
    (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S)
    {p : PolarPoint} (hp : p ∉ annularOpen D) :
    (S.height scalarBeta).decode u p = 0 :=
  ((hS.1 scalarBeta).2.2.2.1 u).2.2.2.1 p hp

/-- Both endpoint constants of the common height are fixed by its coordinates. -/
theorem scalarCommonHeightDecode_endpoint_values
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    (∀ r, r ≤ D.a → ∀ θ, scalarCommonHeightDecode S u (r, θ) = u.2) ∧
      (∀ r, D.b ≤ r → ∀ θ, scalarCommonHeightDecode S u (r, θ) = 0) := by
  obtain ⟨δ, hδ, _, hleft, hright⟩ := hS.2.2.1.2.1
  have hzero (r θ : ℝ) (hr : r ≤ D.a ∨ D.b ≤ r) :
      (S.height scalarBeta).decode u.1 (r, θ) = 0 := by
    apply scalarHeight_decode_eq_zero_outside hS u.1
    intro hp
    rcases hr with hr | hr
    · exact (not_lt_of_ge hr) hp.1.1
    · exact (not_lt_of_ge hr) hp.1.2
  constructor
  · intro r hr θ
    unfold scalarCommonHeightDecode
    rw [hzero r θ (Or.inl hr), hleft r (by linarith), zero_add, mul_one]
  · intro r hr θ
    unfold scalarCommonHeightDecode
    rw [hzero r θ (Or.inr hr), hright r (by linarith), mul_zero, add_zero]

/-- A single zero-integral argument handles intervals beyond either endpoint. -/
private theorem scalarStateProfile_integral_eq_zero_outside
    (hD : IsAccumulatingProfile D) (x : ScalarWeightedState S) {a b : ℝ}
    (h : ∀ t ∈ uIcc a b, t ≤ D.a ∨ D.b ≤ t) :
    (∫ t in a..b, scalarStateProfile D S x t) = 0 := by
  exact (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
    (fun t ht => scalarStateProfile_eq_zero_outside hD x (h t ht))).trans
      intervalIntegral.integral_zero

/-- The normalized primitive is zero on the left and constant on the right. -/
theorem scalarStatePrimitive_endpoint_values
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    (∀ r, r ≤ D.a → scalarStatePrimitive D S x r = 0) ∧
      (∀ r, D.b ≤ r →
        scalarStatePrimitive D S x r = scalarStatePrimitive D S x D.b) := by
  have hw := (scalarStateProfile_contDiff hD hT hS x).continuous
  constructor
  · intro r hr
    apply scalarStateProfile_integral_eq_zero_outside hD x
    intro t ht
    have ht' : t ∈ Icc r D.a := by simpa only [uIcc_of_ge hr] using ht
    exact Or.inl ht'.2
  · intro r hr
    have hz : (∫ t in D.b..r, scalarStateProfile D S x t) = 0 := by
      apply scalarStateProfile_integral_eq_zero_outside hD x
      intro t ht
      have ht' : t ∈ Icc D.b r := by simpa only [uIcc_of_le hr] using ht
      exact Or.inr ht'.1
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable D.a D.b) (hw.intervalIntegrable D.b r)
    rw [hz, add_zero] at he
    exact he.symm

/-- The complete height has exactly the endpoint constants prescribed by the state. -/
theorem scalarStateHeight_endpoint_values
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    (∀ r, r ≤ D.a → ∀ θ, scalarStateHeight D S x (r, θ) = x.2 * x.1.2) ∧
      (∀ r, D.b ≤ r → ∀ θ,
        scalarStateHeight D S x (r, θ) = scalarStatePrimitive D S x D.b) := by
  have hh := scalarStatePrimitive_endpoint_values hD hT hS x
  have hu := scalarCommonHeightDecode_endpoint_values hS (x.1.1.2, x.1.2)
  constructor
  · intro r hr θ
    unfold scalarStateHeight heightFamily Radial.radialHeightField scalarStateIncrement
    rw [hh.1 r hr, hu.1 r hr θ, zero_add]
  · intro r hr θ
    unfold scalarStateHeight heightFamily Radial.radialHeightField scalarStateIncrement
    rw [hh.2 r hr, hu.2 r hr θ, mul_zero, add_zero]

end ContinuousFlexibility.Statements
