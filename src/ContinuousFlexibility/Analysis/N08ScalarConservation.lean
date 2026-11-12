import ContinuousFlexibility.Analysis.N08ScalarFormula
import ContinuousFlexibility.Scalar.WeightedSourceIntegral

/-!
# Conservation of the actual controlled scalar residual

The controlled profile retains the reference support, and the actual height
increment has the same boundary jets as the weighted common-height space.
The discriminant equals one at both endpoints. N01 supplies its positivity
in the open annulus, so the genuine normalized conservation theorem applies
to every parameter, including the removable value at zero.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_stateProfile_eq_zero_outside
    (hD : RadialProfileGeometry D) (x : AnnularState S)
    {r : ℝ} (hr : r ≤ D.a ∨ D.b ≤ r) : stateProfile D S C x r = 0 := by
  rw [stateProfile, hD.2.2.1.2 r hr, zero_mul]

theorem n08_stateProfile_endpointFlat (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) : EndpointFlat D (stateProfile D S C x) := by
  obtain ⟨bounds, hbounds⟩ := hN.1.1
  exact ⟨contDiff_stateProfile_of_n01 hS hT hN x,
    fun _ hr => n08_stateProfile_eq_zero_outside hbounds.1 x hr⟩

theorem n08_stateU_periodic (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    Function.Periodic (stateU S x) (0, Real.pi) :=
  scalarCommonHeightDecode_periodic hS x.1

/-- Reuse the existing common-height endpoint theorem on the same height
coordinates; no representation of the controlled profile is needed here. -/
theorem n08_stateU_endpoint_jets (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) (θ : ℝ) :
    heightRadial (stateU S x) (D.a, θ) = 0 ∧
      heightAngular (stateU S x) (D.a, θ) = 0 ∧
      heightRadial (stateU S x) (D.b, θ) = 0 ∧
      heightAngular (stateU S x) (D.b, θ) = 0 := by
  let y : ScalarWeightedState S := (((0, x.1.1), x.1.2), 0)
  have hy : scalarStateIncrement S y = stateU S x := rfl
  have hu : ContDiff ℝ ∞ (scalarStateIncrement S y) := by
    rw [hy]
    exact n08_stateU_contDiff hT hS x
  simpa only [hy] using scalarStateIncrement_endpoint_jets hS y hu θ

/-- The same boundary calculation covers both physical endpoints. -/
theorem n08_polarDiscriminant_endpoint (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {r : ℝ} (hr : r = D.a ∨ r = D.b) (θ : ℝ) :
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) (r, θ) = 1 := by
  have hw := n08_stateProfile_endpointFlat hT hS hN z.1
  have hjets := n08_stateU_endpoint_jets hT hS z.1 θ
  have hwzero : stateProfile D S C z.1 r = 0 := by
    rcases hr with rfl | rfl
    · exact hw.2 D.a (Or.inl le_rfl)
    · exact hw.2 D.b (Or.inr le_rfl)
  have hk : radialPartial (stateU S z.1) (r, θ) = 0 := by
    rcases hr with rfl | rfl
    · exact hjets.1
    · exact hjets.2.2.1
  have hp : heightAngular (stateU S z.1) (r, θ) = 0 := by
    rcases hr with rfl | rfl
    · exact hjets.2.1
    · exact hjets.2.2.2
  change polarDiscriminant (stateProfile D S C z.1)
    (heightFamily (Radial.radialHeightField (stateRadialHeight D S C z.1))
      (stateU S z.1) z.2) (r, θ) = 1
  rw [n08_polarDiscriminant_radialFamily (n08_stateRadialHeight_contDiff hT hS hN z.1)
    (n08_stateRadialHeight_hasDerivAt hT hS hN z.1) (n08_stateU_contDiff hT hS z.1),
    hwzero, hk, hp]
  norm_num

theorem n08_polarDiscriminant_pos_closed (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ Icc D.a D.b) (θ : ℝ) :
    0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) (r, θ) := by
  rcases eq_or_lt_of_le hr.1 with hleft | hleft
  · rw [n08_polarDiscriminant_endpoint hT hS hN z (Or.inl hleft.symm) θ]
    exact zero_lt_one
  rcases eq_or_lt_of_le hr.2 with hright | hright
  · rw [n08_polarDiscriminant_endpoint hT hS hN z (Or.inr hright) θ]
    exact zero_lt_one
  obtain ⟨_, _, _, _, _, _, _, _, _, hpositive, _⟩ := hN
  have hb := (hpositive z hz hs (r, θ) ⟨⟨hleft, hright⟩, mem_univ θ⟩).2.2.2.2.1
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hb

/-- Conservation for the actual state profile and right-normalized
primitive, uniformly including the genuine value at `q = 0`. -/
theorem n08_scalarResidualField_physicalSourceIntegral_eq_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    physicalSourceIntegral D (scalarResidualField D S C z) = 0 := by
  obtain ⟨bounds, hbounds⟩ := hN.1.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hw := n08_stateProfile_endpointFlat hT hS hN z.1
  have hr : ∀ r ∈ uIcc D.a D.b, r ≠ 0 := by
    intro r hrr
    rw [uIcc_of_le hg.2.1.le] at hrr
    exact (hg.1.trans_le hrr.1).ne'
  have hjets := n08_stateU_endpoint_jets hT hS z.1
  exact integral_mean_normalizedHeightResidual_radialHeight_eq_zero
    (T := Real.pi) (n08_stateRadialHeight_contDiff hT hS hN z.1)
    (n08_stateRadialHeight_hasDerivAt hT hS hN z.1)
    (fun _ _ => hw.1.contDiffAt) (n08_stateU_contDiff hT hS z.1) hr
    (fun p hp => n08_polarDiscriminant_pos_closed hT hS hN hz hs
      (by simpa only [uIcc_of_le hg.2.1.le] using hp.1) p.2)
    (n08_stateU_periodic hS z.1)
    (hw.2 D.a (Or.inl le_rfl)) (hw.2 D.b (Or.inr le_rfl))
    (fun θ _ => (hjets θ).1) (fun θ _ => (hjets θ).2.1)
    (fun θ _ => (hjets θ).2.2.1) (fun θ _ => (hjets θ).2.2.2)

/-- Only equality on the actual open annulus is needed for the physical
source integral; endpoint values are null for the radial integral. -/
theorem n08_physicalSourceIntegral_congr {f g : PolarPoint → ℝ}
    (hab : D.a ≤ D.b) (hfg : ∀ p ∈ annularOpen D, f p = g p) :
    physicalSourceIntegral D f = physicalSourceIntegral D g := by
  unfold physicalSourceIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro r hr
  unfold angularMean
  apply congrArg (fun a : ℝ => (1 / Real.pi) * a)
  apply intervalIntegral.integral_congr
  intro θ _
  exact hfg (r, θ) ⟨hr, mem_univ θ⟩

/-- Compatibility is derived for any decoded realization of the actual
scalar residual, without assuming that it already lies in the source kernel. -/
theorem n08_compatible_of_decode_scalarResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f : (S.height (3 / 4 : ℝ)).Space)
    (hf : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode f p = scalarResidualField D S C z p) : S.Q f = 0 := by
  have hQ : S.Q f = physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode f) := by
    obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hS
    exact hQ f
  obtain ⟨bounds, hbounds⟩ := hN.1.1
  calc
    _ = physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode f) := hQ
    _ = physicalSourceIntegral D (scalarResidualField D S C z) :=
      n08_physicalSourceIntegral_congr hbounds.1.2.1.le hf
    _ = 0 := n08_scalarResidualField_physicalSourceIntegral_eq_zero hT hS hN hz hs

theorem n08_mem_sourceKernel_of_decode_scalarResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f : (S.height (3 / 4 : ℝ)).Space)
    (hf : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode f p = scalarResidualField D S C z p) :
    f ∈ S.Q.toLinearMap.ker :=
  (LinearMap.mem_ker).2 (n08_compatible_of_decode_scalarResidual hT hS hN hz hs f hf)

end ContinuousFlexibility.Statements
