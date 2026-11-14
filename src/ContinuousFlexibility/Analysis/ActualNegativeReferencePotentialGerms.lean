module

public import ContinuousFlexibility.Analysis.ActualNegativeReferenceScalarInverse
public import ContinuousFlexibility.Analysis.LocalMixedProductBounds
public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# The stored negative potential as a germ of its actual scalar formula

The physical inverse point is the literal stored scalar inverse paired
with the same angle. The previously established unit-density potential
identity therefore gives a full planar germ on the canonical half and
transports every mixed derivative, including order zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The actual negative potential is radial on the whole canonical open
half. Its radial representative uses precisely the stored height and
inverse slices, without a new extension or inverse selection. -/
theorem n04Coordinates_actual_reference_negative_potential_germ
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
    let H := fun r : ℝ => K.height z₀ k (r, 0)
    let χ := fun ξ : ℝ => (K.inverseChart z₀ k (ξ, 0)).1
    let V := fun ξ : ℝ => D.w (χ ξ) * H (χ ξ) ^ 3 *
      deriv (fun r => D.w r * deriv H r) (χ ξ)
    ∀ p ∈ canonicalOpen S K k,
      K.potential z₀ k =ᶠ[𝓝 p] (fun q : PolarPoint => V q.1) ∧
      ∀ a b, mixedDerivative a b (K.potential z₀ k) p =
        if b = 0 then iteratedDeriv a V p.1 else 0 := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let H := fun r : ℝ => K.height z₀ k (r, 0)
  let χ := fun ξ : ℝ => (K.inverseChart z₀ k (ξ, 0)).1
  let V := fun ξ : ℝ => D.w (χ ξ) * H (χ ξ) ^ 3 *
    deriv (fun r => D.w r * deriv H r) (χ ξ)
  have hgeometry := n04Coordinates_actual_reference_negative_scalar_inverse
    hT hS hN hfield e m side
  have hinverse : ∀ q ∈ canonicalOpen S K k,
      K.inverseChart z₀ k q = (χ q.1, q.2) := hgeometry.2.2.2.2.2.2.2
  intro p hp
  have hnear : K.potential z₀ k =ᶠ[𝓝 p] (fun q : PolarPoint => V q.1) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have hv := n04Coordinates_actual_reference_negative_potential_formula
      hT hS hN hfield e m side hq
    change K.potential z₀ k q = D.w (K.inverseChart z₀ k q).1 *
      H (K.inverseChart z₀ k q).1 ^ 3 *
        deriv (fun r => D.w r * deriv H r) (K.inverseChart z₀ k q).1 at hv
    rw [hinverse q hq] at hv
    exact hv
  refine ⟨hnear, ?_⟩
  intro a b
  exact (mixedDerivative_eq_of_germ hnear a b).trans
    (n08_mixedDerivative_radial V a b p)

end ContinuousFlexibility.Analysis
