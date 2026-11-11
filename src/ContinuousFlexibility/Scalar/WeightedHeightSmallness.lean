import ContinuousFlexibility.Scalar.WeightedHeightGerms
import ContinuousFlexibility.Scalar.WeightedGeometryLowJets

/-!
# Uniform pointwise smallness on an actual state neighborhood

The fixed fourth height seminorm controls the decoded field at every
physical point. Therefore a continuous weighted state map vanishing at the
center is uniformly small on one neighborhood, simultaneously at all points.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarHeight_decode_uniform_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ScalarHeightSpace S) (p : PolarPoint),
      |(S.height scalarBeta).decode u p| ≤ C * scalarHeightGrading S 4 u := by
  obtain ⟨J, hJ, hJu⟩ := scalarMixedDerivative_le_reference_grading hD hT hS 0 0 4 (by omega)
  obtain ⟨M, hM, hMw⟩ := referenceProfile_uniform_upper_bound hD
  refine ⟨1 + J * M, by positivity, ?_⟩
  intro u p
  by_cases hp : p ∈ annularOpen D
  · have hjet : |(S.height scalarBeta).decode u p| ≤
        J * scalarHeightGrading S 4 u * D.w p.1 := by
      simpa only [mixedDerivative, iteratedDeriv_zero] using hJu u p hp
    calc
      _ ≤ J * scalarHeightGrading S 4 u * D.w p.1 := hjet
      _ ≤ J * scalarHeightGrading S 4 u * M :=
        mul_le_mul_of_nonneg_left (hMw p.1 hp.1)
          (mul_nonneg hJ (apply_nonneg _ _))
      _ = (J * M) * scalarHeightGrading S 4 u := by ring
      _ ≤ (1 + J * M) * scalarHeightGrading S 4 u :=
        mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
  · rw [scalarHeight_decode_eq_zero_outside hS u hp, abs_zero]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)

theorem UniformTameGerm.scalarDecode_small
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {x0 : X} {f : X → ScalarHeightSpace S}
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hf0 : f x0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x in 𝓝 x0, ∀ z : PolarPoint, |(S.height scalarBeta).decode (f x) z| < δ := by
  obtain ⟨C, hC, hCu⟩ := scalarHeight_decode_uniform_bound hD hT hS
  have hcont : ContinuousAt (fun x => scalarHeightGrading S 4 (f x)) x0 :=
    (continuous_scalarHeightGrading S 4).continuousAt.comp hf.continuousAt
  have hval : scalarHeightGrading S 4 (f x0) < δ / C := by
    rw [hf0]
    calc
      scalarHeightGrading S 4 (0 : ScalarHeightSpace S) = 0 :=
        (scalarHeightGrading S 4).map_zero'
      _ < δ / C := div_pos hδ hC
  have hevent : ∀ᶠ x in 𝓝 x0, scalarHeightGrading S 4 (f x) < δ / C :=
    hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hevent] with x hx z
  apply (hCu (f x) z).trans_lt
  calc
    C * scalarHeightGrading S 4 (f x) < C * (δ / C) :=
      mul_lt_mul_of_pos_left hx hC
    _ = δ := by field_simp [hC.ne']

end ContinuousFlexibility.Statements
