import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity
import ContinuousFlexibility.Analysis.N04bReferenceActualTravel
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
import ContinuousFlexibility.Analysis.N04bActualRootInterior

/-!
# Radial fields of the actual negative reference atlas

The actual reference travel chart fixes its angular coordinate. The
stored chart therefore has a radial first coordinate on the entire open
negative component. Its actual unit principal density, the reference
coefficient a = w, and positivity determine the height on each circle.
No extension outside that open component is assumed to be radial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem radial_chart_fderiv
    {F : PolarPoint → PolarPoint} {a b r : ℝ}
    (hr : r ∈ Ioo a b) (hF : DifferentiableAt ℝ F (r, 0))
    (he : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F p = ((F (p.1, 0)).1, p.2)) (θ : ℝ) (v : PolarPoint) :
    fderiv ℝ F (r, θ) v =
      (deriv (fun s : ℝ => (F (s, 0)).1) r * v.1, v.2) := by
  let f : ℝ → ℝ := fun s => (F (s, 0)).1
  have hf : HasDerivAt f (deriv f r) r :=
    (hasDerivAt_radial_slice hF.fst).differentiableAt.hasDerivAt
  have hd := (hf.comp_hasFDerivAt (f := fun p : PolarPoint => p.1)
    (r, θ) (hasFDerivAt_fst (p := (r, θ)))).prodMk
    (hasFDerivAt_snd (p := (r, θ)))
  have hnear : F =ᶠ[𝓝 (r, θ)] (fun p : PolarPoint => (f p.1, p.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (r, θ) ∈ Ioo a b ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ _⟩)]
      with p hp
    exact he p hp
  rw [hnear.fderiv_eq, hd.fderiv]
  simp only [f, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

private theorem radial_height_of_unit_density
    {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ}
    {A : SymmetricCoefficients} {w : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), DifferentiableAt ℝ F p)
    (hH : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < H p)
    (he : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F p = ((F (p.1, 0)).1, p.2))
    (ha : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), A.a p = w p.1)
    (hunit : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      (coordinatePrincipalDensity A F H).a p = 1)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ (univ : Set ℝ)) :
    H p = H (p.1, 0) := by
  let j : ℝ := deriv (fun s : ℝ => (F (s, 0)).1) p.1
  let B : ℝ := (w p.1 * j ^ 2) / |j|
  have hp₀ : (p.1, 0) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hD (θ : ℝ) (v : PolarPoint) :
      fderiv ℝ F (p.1, θ) v = (j * v.1, v.2) :=
    radial_chart_fderiv hp.1 (hF _ hp₀) he θ v
  have hJ (θ : ℝ) : planeJacobian F (p.1, θ) = j := by
    simp only [planeJacobian, hD, mul_one, mul_zero, sub_zero]
  have hn (θ : ℝ) : H (p.1, θ) ^ 2 * B = 1 := by
    have h := hunit (p.1, θ) ⟨hp.1, mem_univ _⟩
    have haθ := ha (p.1, θ) ⟨hp.1, mem_univ _⟩
    have heq : H (p.1, θ) ^ 2 / |j| * (w p.1 * j ^ 2) = 1 := by
      simpa only [coordinatePrincipalDensity, coefficientQuadratic, hD, hJ, haθ,
        mul_one, mul_zero, zero_pow two_ne_zero, add_zero] using h
    calc
      H (p.1, θ) ^ 2 * B = H (p.1, θ) ^ 2 / |j| * (w p.1 * j ^ 2) := by
        dsimp only [B]
        ring
      _ = 1 := heq
  have hB : B ≠ 0 := by
    intro hzero
    have h := hn 0
    rw [hzero, mul_zero] at h
    exact zero_ne_one h
  have hsquare : H p ^ 2 = H (p.1, 0) ^ 2 :=
    (mul_right_cancel₀ hB) ((hn p.2).trans (hn 0).symm)
  exact (sq_eq_sq₀ (hH p hp).le (hH _ hp₀).le).mp hsquare

/-- Actual stored reference fields are smooth and radial on the whole
open negative component. The full chart still has its angular identity
coordinate; only the scalar height is angle-independent. -/
theorem n04Coordinates_actual_reference_negative_radial_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (m : ℕ) (side : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := e.symm (.inl (m, side))
    let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
    let Ω := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
    ContDiffOn ℝ ∞ (K.chart z₀ k) Ω ∧
      ContDiffOn ℝ ∞ (K.height z₀ k) Ω ∧
      (∀ p ∈ Ω, K.chart z₀ k p = ((K.chart z₀ k (p.1, 0)).1, p.2)) ∧
      (∀ p ∈ Ω, K.height z₀ k p = K.height z₀ k (p.1, 0)) ∧
      (∀ p ∈ Ω, 0 < K.height z₀ k p) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let Ω := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  have hz₀ : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hi : e k = .inl (m, side) := e.apply_symm_apply _
  have hreg (p : PolarPoint) (hp : p ∈ Ω) :
      ContDiffAt ℝ ∞ (K.chart z₀ k) p ∧
        ContDiffAt ℝ ∞ (K.height z₀ k) p ∧ 0 < K.height z₀ k p := by
    have hg := n04bActualTypedAtlas_negative_component_germs
      hT hS hN hfield e hz₀ hs₀ k m side hi hp
    have hr := n04b_actualRootPhysical_regular_at hN hS hT hfield hz₀ hs₀ m side hp
    refine ⟨hr.1.congr_of_eventuallyEq hg.1,
      hr.2.1.congr_of_eventuallyEq hg.2, ?_⟩
    rw [hg.2.self_of_nhds]
    exact hr.2.2.2
  have hvalue (p : PolarPoint) (hp : p ∈ Ω) :
      K.chart z₀ k p =
        (n04bRootHalfCoordinate (C.travel m) side
          (opticalTravel D.w (C.left m) p.1), p.2) := by
    have hg := n04bActualTypedAtlas_negative_component_germs
      hT hS hN hfield e hz₀ hs₀ k m side hi hp
    rw [hg.1.self_of_nhds]
    change n04bRootStripChart (C.travel m) side
      (n04bActualTravelChart S C L z₀ m p) = _
    rw [n04b_reference_actualTravelChart hN.1.1.2.2.1 hT hS hN hfield m
      ⟨hp.1.1.le, hp.1.2.le⟩ p.2]
    rfl
  have hshape (p : PolarPoint) (hp : p ∈ Ω) :
      K.chart z₀ k p = ((K.chart z₀ k (p.1, 0)).1, p.2) := by
    rw [hvalue p hp, hvalue (p.1, 0) ⟨hp.1, mem_univ _⟩]
  refine ⟨fun p hp => (hreg p hp).1.contDiffWithinAt,
    fun p hp => (hreg p hp).2.1.contDiffWithinAt, hshape, ?_,
    fun p hp => (hreg p hp).2.2⟩
  intro p hp
  exact radial_height_of_unit_density
    (F := K.chart z₀ k) (H := K.height z₀ k)
    (A := L.coefficients z₀) (w := D.w)
    (a := C.left m) (b := C.right m)
    (fun q hq => (hreg q hq).1.differentiableAt (by simp))
    (fun q hq => (hreg q hq).2.2) hshape
    (fun q _ => (hN.2.1 z₀ hz₀ hs₀ q).trans (hN.1.1.reference_coefficients q).1)
    (fun q hq => (n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e hz₀ hs₀ k m side hi hq).1) hp

end ContinuousFlexibility.Analysis

