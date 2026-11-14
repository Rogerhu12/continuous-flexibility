module

public import ContinuousFlexibility.Analysis.ActualNegativeReferenceScalarInverse
public import ContinuousFlexibility.Analysis.RadialUnitDensityInverseJets

/-!
# The actual negative reference geometric fields

The literal chart, inverse and height slices determine every geometric
field on the true half. Unit density removes the absolute Jacobian from
its reciprocal and from the canonical source factor. These identities
are independent of the material estimates and introduce no new fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- Exact shape, range, Jacobian and source identities for the original
stored negative reference fields. The inverse point keeps its real angle. -/
theorem n04Coordinates_actual_reference_negative_geometry_fields
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
    let cut := n04bActualReferenceCut hN
    let I := Ioo (n04bNegativeLeft C cut (m, side))
      (n04bNegativeRight C cut (m, side))
    let J := Ioo (K.left k) (K.right k)
    let Y := fun r : ℝ => (K.chart z₀ k (r, 0)).1
    let H := fun r : ℝ => K.height z₀ k (r, 0)
    let χ := fun ξ : ℝ => (K.inverseChart z₀ k (ξ, 0)).1
    (∀ p ∈ I ×ˢ (univ : Set ℝ),
      K.chart z₀ k p = (Y p.1, p.2) ∧ K.height z₀ k p = H p.1 ∧
        Y p.1 ∈ J ∧ 0 < H p.1 ∧
        |planeJacobian (K.chart z₀ k) p| = H p.1 ^ (-2 : ℝ) * (D.w p.1)⁻¹ ∧
        |planeJacobian (K.chart z₀ k) p|⁻¹ = H p.1 ^ 2 * D.w p.1) ∧
    ∀ p ∈ canonicalOpen S K k,
      K.inverseChart z₀ k p = (χ p.1, p.2) ∧ χ p.1 ∈ I ∧
        canonicalSource S K z₀ k (fun _ => 1) p = H (χ p.1) ^ 3 * D.w (χ p.1) ∧
        (canonicalSource S K z₀ k (fun _ => 1) p)⁻¹ =
          H (χ p.1) ^ (-3 : ℝ) * (D.w (χ p.1))⁻¹ := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let cut := n04bActualReferenceCut hN
  let I := Ioo (n04bNegativeLeft C cut (m, side))
    (n04bNegativeRight C cut (m, side))
  let J := Ioo (K.left k) (K.right k)
  let F := K.chart z₀ k
  let Y := fun r : ℝ => (F (r, 0)).1
  let H := fun r : ℝ => K.height z₀ k (r, 0)
  let χ := fun ξ : ℝ => (K.inverseChart z₀ k (ξ, 0)).1
  have hi : e k = .inl (m, side) := e.apply_symm_apply _
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hA : Blueprint.N04PartA D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hphysical : physicalPieceOpen S K z₀ k = I ×ˢ (univ : Set ℝ) := by
    rw [hA.referenceDomain k]
    change Ioo (n04bReferenceTypedLeft C cut (e k))
      (n04bReferenceTypedRight C cut (e k)) ×ˢ (univ : Set ℝ) = _
    rw [hi]
    rfl
  have hmapF : MapsTo F (I ×ˢ (univ : Set ℝ)) (canonicalOpen S K k) := by
    simpa only [hphysical] using (hA.charts z₀ href hsref k).1
  have hradial := n04Coordinates_actual_reference_negative_radial_fields
    hT hS hN hfield e m side
  have hscalar := n04Coordinates_actual_reference_negative_scalar_inverse
    hT hS hN hfield e m side
  have hunit : ∀ r ∈ I, 0 < H r ∧ H r ^ 2 * D.w r * |deriv Y r| = 1 :=
    hscalar.2.2.2.2.2.2.1
  have hphysicalFields (p : PolarPoint) (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
      F p = (Y p.1, p.2) ∧ K.height z₀ k p = H p.1 ∧
        Y p.1 ∈ J ∧ 0 < H p.1 ∧
        |planeJacobian F p| = H p.1 ^ (-2 : ℝ) * (D.w p.1)⁻¹ ∧
        |planeJacobian F p|⁻¹ = H p.1 ^ 2 * D.w p.1 := by
    have hpwhole : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hp.1,
        mem_univ _⟩
    have hshape : F p = (Y p.1, p.2) := hradial.2.2.1 p hpwhole
    have hheight : K.height z₀ k p = H p.1 := hradial.2.2.2.1 p hpwhole
    have hYrange : Y p.1 ∈ J := by
      have hh := hmapF hp
      rw [hshape] at hh
      exact hh.1
    obtain ⟨hFg, hYd⟩ := radial_reference_chart_germ_on_strip
      hradial.1 hradial.2.2.1 hpwhole
    have hJ : planeJacobian F p = deriv Y p.1 := by
      calc
        _ = planeJacobian (positiveReferenceCylinderChart Y) p := by
          have hfd : fderiv ℝ F p = fderiv ℝ (positiveReferenceCylinderChart Y) p :=
            hFg.fderiv_eq
          simp only [planeJacobian, hfd]
        _ = _ := planeJacobian_positiveReferenceCylinderChart hYd
    have hn := radialUnit_scalar_normalization (hunit p.1 hp.1).2
    refine ⟨hshape, hheight, hYrange, (hunit p.1 hp.1).1, ?_, ?_⟩
    · rw [hJ]
      exact hn.2.2
    · rw [hJ]
      exact hn.2.1
  refine ⟨hphysicalFields, ?_⟩
  intro p hp
  have hG : K.inverseChart z₀ k p = (χ p.1, p.2) := hscalar.2.2.2.2.2.2.2 p hp
  have hx : χ p.1 ∈ I := hscalar.2.2.2.1 hp.1
  have hd := hphysicalFields (χ p.1, p.2) ⟨hx, mem_univ _⟩
  have hsource : canonicalSource S K z₀ k (fun _ => 1) p =
      H (χ p.1) ^ 3 * D.w (χ p.1) := by
    change K.height z₀ k (K.inverseChart z₀ k p) * 1 /
      |planeJacobian F (K.inverseChart z₀ k p)| = _
    rw [hG, mul_one, hd.2.1, div_eq_mul_inv, hd.2.2.2.2.2]
    ring
  refine ⟨hG, hx, hsource, ?_⟩
  change (canonicalSource S K z₀ k (fun _ => 1) p)⁻¹ =
    H (χ p.1) ^ (-3 : ℝ) * (D.w (χ p.1))⁻¹
  rw [hsource]
  simp only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, mul_inv]

end ContinuousFlexibility.Analysis
