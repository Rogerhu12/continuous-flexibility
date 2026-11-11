import ContinuousFlexibility.Scalar.WeightedCoefficientRegularity
import ContinuousFlexibility.Scalar.WeightedFlatProducts
import ContinuousFlexibility.Scalar.GreenIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Endpoint flux and Green symmetry on the weighted common height domain

The coefficient decoder fixes the actual coefficient values outside the
physical annulus.  In particular the normal coefficient row vanishes at
both endpoints.  No boundary condition is imposed on the common heights,
whose left constants remain free.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateNormalFlux_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x)) (u : ScalarCommonHeight S) :
    ContDiff ℝ ∞ (scalarStateNormalFlux D S x u) :=
  contDiff_iff_contDiffAt.mpr fun p =>
    contDiffAt_symmetricNormalFlux hA.contDiffAt hB.contDiffAt
      (scalarCommonHeightDecode_contDiff hT hS u).contDiffAt

theorem scalarStateNormalFlux_uniformFlatJets_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) : UniformFlatJets D (scalarStateNormalFlux D S x u) := by
  obtain ⟨hA, hB⟩ := scalarStateAB_contDiff_and_flatJets_of_decode hD hT hS x c hc
  have hu := scalarCommonHeightDecode_contDiff hT hS u
  have hur : ContDiff ℝ ∞ (radialPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_radialPartial hu.contDiffAt (by simp)
  have hut : ContDiff ℝ ∞ (angularPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hu.contDiffAt (by simp)
  exact (hA.2.mul_smooth hA.1 hur).add (hB.2.mul_smooth hB.1 hut)
    (hA.1.mul hur) (hB.1.mul hut)

theorem scalarStateNormalFlux_eq_zero_outside_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) {r : ℝ} (hr : r ≤ D.a ∨ D.b ≤ r) (θ : ℝ) :
    scalarStateNormalFlux D S x u (r, θ) = 0 := by
  have hp : (r, θ) ∉ annularOpen D := by
    intro hp
    rcases hr with hr | hr
    · exact (not_lt_of_ge hr) hp.1.1
    · exact (not_lt_of_ge hr) hp.1.2
  obtain ⟨hA, hB⟩ := scalarStateAB_eq_of_coefficient_decode x c hc
  have hw := hD.choose_spec.1.2.2.1.2 r hr
  simp only [scalarStateNormalFlux, symmetricNormalFlux, hA, hB,
    scalarFieldDecode_eq_zero_outside hT hS (c 0) hp,
    scalarFieldDecode_eq_zero_outside hT hS (c 1) hp, hw, zero_add, zero_mul]

theorem scalarStateNormalFlux_endpoint_values_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) (θ : ℝ) :
    scalarStateNormalFlux D S x u (D.a, θ) = 0 ∧
      scalarStateNormalFlux D S x u (D.b, θ) = 0 :=
  ⟨scalarStateNormalFlux_eq_zero_outside_of_decode hD hT hS x c hc u (Or.inl le_rfl) θ,
    scalarStateNormalFlux_eq_zero_outside_of_decode hD hT hS x c hc u (Or.inr le_rfl) θ⟩

theorem scalarStateNormalFlux_endpoint_limits_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) (θ : ℝ) :
    Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ)) (𝓝[>] D.a) (𝓝 0) ∧
      Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ)) (𝓝[<] D.b) (𝓝 0) := by
  obtain ⟨hA, hB⟩ := scalarStateAB_contDiff_and_flatJets_of_decode hD hT hS x c hc
  have hflux := (scalarStateNormalFlux_contDiff hT hS x hA.1 hB.1 u).continuous
  have hs : Continuous (fun r => scalarStateNormalFlux D S x u (r, θ)) :=
    hflux.comp (continuous_id.prodMk continuous_const)
  have ht (r : ℝ) (s : Set ℝ) :
      Tendsto (fun t => scalarStateNormalFlux D S x u (t, θ)) (𝓝[s] r)
        (𝓝 (scalarStateNormalFlux D S x u (r, θ))) :=
    (hs.continuousAt (x := r)).tendsto.mono_left nhdsWithin_le_nhds
  have hend := scalarStateNormalFlux_endpoint_values_of_decode hD hT hS x c hc u θ
  exact ⟨by simpa only [hend.1] using ht D.a (Ioi D.a),
    by simpa only [hend.2] using ht D.b (Iio D.b)⟩

theorem scalarStateOperator_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x)) (u : ScalarCommonHeight S) :
    ContDiff ℝ ∞ (scalarStateOperator D S x u) := by
  have hu := scalarCommonHeightDecode_contDiff hT hS u
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (contDiffAt_radialPartial
    (contDiffAt_symmetricNormalFlux hA.contDiffAt hB.contDiffAt hu.contDiffAt) (by simp)).add
    (contDiffAt_angularPartial
      (contDiffAt_symmetricAngularFlux hB.contDiffAt hC.contDiffAt hu.contDiffAt) (by simp))

theorem scalarGreenIntegrand_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x)) (u v : ScalarCommonHeight S) :
    ContDiff ℝ ∞ (ScalarGreenIntegrand D S x u v) :=
  ((scalarCommonHeightDecode_contDiff hT hS u).mul
    (scalarStateOperator_contDiff hT hS x hA hB hC v)).sub
    ((scalarCommonHeightDecode_contDiff hT hS v).mul
      (scalarStateOperator_contDiff hT hS x hA hB hC u))

theorem scalarGreen_identity_of_coefficient_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u v : ScalarCommonHeight S) :
    IntervalIntegrable (fun r => ∫ θ in (0 : ℝ)..Real.pi,
      ScalarGreenIntegrand D S x u v (r, θ)) volume D.a D.b ∧
      scalarAnnularIntegral D (ScalarGreenIntegrand D S x u v) = 0 := by
  obtain ⟨hA, hB⟩ := scalarStateAB_contDiff_and_flatJets_of_decode hD hT hS x c hc
  have hC := (scalarStateCorrectedC_contDiff_and_flatJets_of_decode hD hT hS x c hc).1
  have hu := scalarCommonHeightDecode_contDiff hT hS u
  have hv := scalarCommonHeightDecode_contDiff hT hS v
  constructor
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => ScalarGreenIntegrand D S x u v (r, θ))
      (scalarGreenIntegrand_contDiff hT hS x hA.1 hB.1 hC u v).continuous
      0 Real.pi).intervalIntegrable D.a D.b
  · have hboundary (r : ℝ) (hr : r ≤ D.a ∨ D.b ≤ r) (θ : ℝ) :
        greenNormalFlux (scalarStateA D S x) (scalarStateB D S x)
          (scalarCommonHeightDecode S u) (scalarCommonHeightDecode S v) (r, θ) = 0 := by
      change scalarCommonHeightDecode S u (r, θ) * scalarStateNormalFlux D S x v (r, θ) -
        scalarCommonHeightDecode S v (r, θ) * scalarStateNormalFlux D S x u (r, θ) = 0
      rw [scalarStateNormalFlux_eq_zero_outside_of_decode hD hT hS x c hc v hr θ,
        scalarStateNormalFlux_eq_zero_outside_of_decode hD hT hS x c hc u hr θ,
        mul_zero, mul_zero, sub_self]
    exact integral_heightCorrected_green_eq_zero
      (fun _ _ => hA.1.contDiffAt) (fun _ _ => hB.1.contDiffAt)
      (fun _ _ => hC.contDiffAt) (fun _ _ => hu.contDiffAt) (fun _ _ => hv.contDiffAt)
      (scalarStateHeight_periodic hS x) (scalarCommonHeightDecode_periodic hS u)
      (scalarCommonHeightDecode_periodic hS v)
      (fun θ _ => hboundary D.a (Or.inl le_rfl) θ)
      (fun θ _ => hboundary D.b (Or.inr le_rfl) θ)

/-- Both final Green clauses of `IsWeightedS05` follow on any set where the
three actual coefficient differences have their prescribed decoding. -/
theorem weightedScalar_green_clauses
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (U : Set (ScalarWeightedState S))
    (c : ScalarWeightedState S → Fin 3 → ScalarFieldSpace S)
    (hc : ∀ x ∈ U, ∀ i p,
      scalarFieldDecode S (c x i) p = scalarCoefficientComponent D S x i p) :
    (∀ x ∈ U, ∀ u,
      UniformFlatJets D (scalarStateNormalFlux D S x u) ∧
      (∀ θ, scalarStateNormalFlux D S x u (D.a, θ) = 0 ∧
        scalarStateNormalFlux D S x u (D.b, θ) = 0) ∧
      (∀ θ, Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ))
        (𝓝[>] D.a) (𝓝 0) ∧
        Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ)) (𝓝[<] D.b) (𝓝 0))) ∧
    (∀ x ∈ U, ∀ u v,
      IntervalIntegrable (fun r => ∫ θ in (0 : ℝ)..Real.pi,
        ScalarGreenIntegrand D S x u v (r, θ)) volume D.a D.b ∧
      scalarAnnularIntegral D (ScalarGreenIntegrand D S x u v) = 0) := by
  constructor
  · intro x hx u
    exact ⟨scalarStateNormalFlux_uniformFlatJets_of_decode hD hT hS x (c x) (hc x hx) u,
      scalarStateNormalFlux_endpoint_values_of_decode hD hT hS x (c x) (hc x hx) u,
      scalarStateNormalFlux_endpoint_limits_of_decode hD hT hS x (c x) (hc x hx) u⟩
  · intro x hx u v
    exact scalarGreen_identity_of_coefficient_decode hD hT hS x (c x) (hc x hx) u v

end ContinuousFlexibility.Statements
