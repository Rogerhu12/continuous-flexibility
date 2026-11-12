import ContinuousFlexibility.Analysis.ActualNegativeReferencePotentialFormula

/-!
# The actual scalar inverse on a negative reference half

The same stored planar inverse is cylindrical on the reference half.
The scalar functions below are its literal zero-angle slices. Their
inverse identities and unit radial normalization follow from the actual
chart geometry and density, without selecting another inverse function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- Literal slices of the original typed atlas give a genuine scalar
inverse and the unit radial density on the same actual physical half. -/
theorem n04Coordinates_actual_reference_negative_scalar_inverse
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
    ContDiffOn ℝ ∞ Y I ∧ ContDiffOn ℝ ∞ H I ∧
      ContDiffOn ℝ ∞ χ J ∧ MapsTo χ J I ∧
      (∀ ξ ∈ J, Y (χ ξ) = ξ) ∧ (∀ r ∈ I, χ (Y r) = r) ∧
      (∀ r ∈ I, 0 < H r ∧ H r ^ 2 * D.w r * |deriv Y r| = 1) ∧
      ∀ p ∈ canonicalOpen S K k, K.inverseChart z₀ k p = (χ p.1, p.2) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let cut := n04bActualReferenceCut hN
  let I := Ioo (n04bNegativeLeft C cut (m, side))
    (n04bNegativeRight C cut (m, side))
  let J := Ioo (K.left k) (K.right k)
  let F := K.chart z₀ k
  let G := K.inverseChart z₀ k
  let Y := fun r : ℝ => (F (r, 0)).1
  let H := fun r : ℝ => K.height z₀ k (r, 0)
  let χ := fun ξ : ℝ => (G (ξ, 0)).1
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
  have hcharts := hA.charts z₀ href hsref k
  rw [hphysical] at hcharts
  rcases hcharts with ⟨hmapF, hmapG, hleft, hright, hF, hG, hH, hregular⟩
  have hradial := n04Coordinates_actual_reference_negative_radial_fields
    hT hS hN hfield e m side
  have hwhole {r : ℝ} (hr : r ∈ I) : r ∈ Ioo (C.left m) (C.right m) :=
    n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hr
  have hshape (p : PolarPoint) (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
      F p = (Y p.1, p.2) := hradial.2.2.1 p ⟨hwhole hp.1, mem_univ _⟩
  have hHeight (p : PolarPoint) (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
      K.height z₀ k p = H p.1 := hradial.2.2.2.1 p ⟨hwhole hp.1, mem_univ _⟩
  have hY : ContDiffOn ℝ ∞ Y I := by
    intro r hr
    exact ((hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hr, mem_univ (0 : ℝ)⟩)).fst.comp r
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hHs : ContDiffOn ℝ ∞ H I := by
    intro r hr
    exact ((hH.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hr, mem_univ (0 : ℝ)⟩)).comp r
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hχ : ContDiffOn ℝ ∞ χ J := by
    intro ξ hξ
    exact ((hG.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hξ, mem_univ (0 : ℝ)⟩)).fst.comp ξ
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hmapχ : MapsTo χ J I := fun ξ hξ => (hmapG ⟨hξ, mem_univ (0 : ℝ)⟩).1
  have hYχ (ξ : ℝ) (hξ : ξ ∈ J) : Y (χ ξ) = ξ := by
    have hp : (ξ, (0 : ℝ)) ∈ canonicalOpen S K k := ⟨hξ, mem_univ _⟩
    have he := (hshape (G (ξ, 0)) (hmapG hp)).symm.trans (hright (ξ, 0) hp)
    exact congrArg (fun q : PolarPoint => q.1) he
  have hχY (r : ℝ) (hr : r ∈ I) : χ (Y r) = r := by
    have hp : (r, (0 : ℝ)) ∈ I ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
    have he := hleft (r, 0) hp
    rw [hshape (r, 0) hp] at he
    exact congrArg (fun q : PolarPoint => q.1) he
  refine ⟨hY, hHs, hχ, hmapχ, hYχ, hχY, ?_, ?_⟩
  · intro r hr
    have hp : (r, (0 : ℝ)) ∈ I ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
    have hYat := hY.contDiffAt (isOpen_Ioo.mem_nhds hr)
    have hFg : F =ᶠ[𝓝 (r, (0 : ℝ))] positiveReferenceCylinderChart Y := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
      exact hshape q hq
    have hHg : K.height z₀ k =ᶠ[𝓝 (r, (0 : ℝ))]
        (fun q : PolarPoint => H q.1) := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
      exact hHeight q hq
    have he := (coordinatePrincipalDensity_component_eventuallyEq
      (A := L.coefficients z₀) hFg hHg 0).self_of_nhds
    norm_num only [canonicalCoefficientComponent] at he
    have hf := (coordinatePrincipalDensity_radial_cylinder
      (A := L.coefficients z₀) (H := H) (p := (r, 0))
      (hYat.differentiableAt (by simp))).1
    have ha : (L.coefficients z₀).a (r, 0) = D.w r :=
      (hN.2.1 z₀ href hsref (r, 0)).trans (hN.1.1.reference_coefficients (r, 0)).1
    have hu := (n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e href hsref k m side hi ⟨hwhole hr, mem_univ (0 : ℝ)⟩).1
    have hdensity : H r ^ 2 / |deriv Y r| * (D.w r * deriv Y r ^ 2) = 1 := by
      have hn := hf.symm.trans (he.symm.trans hu)
      simpa only [ha] using hn
    have hj : |deriv Y r| ≠ 0 := by
      intro hj
      rw [hj, div_zero, zero_mul] at hdensity
      exact zero_ne_one hdensity
    refine ⟨(hregular (r, 0) hp).1, ?_⟩
    apply mul_right_cancel₀ hj
    calc
      (H r ^ 2 * D.w r * |deriv Y r|) * |deriv Y r| =
          H r ^ 2 * (D.w r * deriv Y r ^ 2) := by rw [← sq_abs (deriv Y r)]; ring
      _ = |deriv Y r| := by
        have hn := congrArg (fun t : ℝ => t * |deriv Y r|) hdensity
        field_simp [hj] at hn
        nlinarith only [hn]
      _ = 1 * |deriv Y r| := (one_mul _).symm
  · intro p hp
    have hq : (χ p.1, p.2) ∈ I ×ˢ (univ : Set ℝ) :=
      ⟨hmapχ hp.1, mem_univ _⟩
    have hfq : F (χ p.1, p.2) = p := by
      rw [hshape _ hq, hYχ p.1 hp.1]
    have he := hleft (χ p.1, p.2) hq
    rw [hfq] at he
    exact he

end ContinuousFlexibility.Analysis
