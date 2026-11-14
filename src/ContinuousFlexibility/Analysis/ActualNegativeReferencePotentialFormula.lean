import ContinuousFlexibility.Analysis.RadialReferencePotentialGerms
import ContinuousFlexibility.Analysis.ActualReferenceNegativeRadialFields
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The actual negative reference potential after unit-density cancellation

The reference height and chart are the stored fields of the original
typed atlas. Their unit radial density removes the inverse Jacobian from
the scalar potential. The resulting identity uses the actual zero-angle
height slice and its ordinary derivatives; it does not assume a uniform
estimate on that slice throughout the negative component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem radial_unit_density_inverse_slope
    {w h j : ℝ} (hu : h ^ 2 / |j| * (w * j ^ 2) = 1) :
    |j|⁻¹ = h ^ 2 * w := by
  have hj : |j| ≠ 0 := by
    intro he
    rw [he, div_zero, zero_mul] at hu
    exact zero_ne_one hu
  have hnorm : h ^ 2 * w * |j| = 1 := by
    apply mul_right_cancel₀ hj
    calc
      _ = h ^ 2 * (w * j ^ 2) := by rw [← sq_abs j]; ring
      _ = |j| := by
        have he := congrArg (fun x : ℝ => x * |j|) hu
        field_simp [hj] at he
        nlinarith only [he]
      _ = 1 * |j| := (one_mul _).symm
  exact inv_eq_of_mul_eq_one_left hnorm

/-- A genuine radial unit density removes the inverse slope from the
potential formula. The mixed physical coefficient is derived to be zero
from that same density rather than supplied as a new condition. -/
theorem inverseChartPotential_radial_unit_formula_on_strip
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {w : ℝ → ℝ} {l r : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hshape : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), F q = ((F (q.1, 0)).1, q.2))
    (hheight : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), h q = h (q.1, 0))
    (ha : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), A.a q = w q.1)
    (hunit : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      (coordinatePrincipalDensity A F h).a q = 1 ∧
        (coordinatePrincipalDensity A F h).b q = 0)
    {p : PolarPoint} (hp : G p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    inverseChartPotential A F G h p =
      w (G p).1 * h ((G p).1, 0) ^ 3 *
        deriv (fun t => w t * deriv (fun s => h (s, 0)) t) (G p).1 := by
  have hb (q : PolarPoint) (hq : q ∈ Ioo l r ×ˢ (univ : Set ℝ)) : A.b q = 0 :=
    physical_mixed_zero_of_radial_unit_density hF hshape hheight hunit hq
  obtain ⟨hFg, hY⟩ := radial_reference_chart_germ_on_strip hF hshape hp
  have hHg : h =ᶠ[𝓝 (G p)] (fun q : PolarPoint => h (q.1, 0)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hheight q hq
  have hcomponent := (coordinatePrincipalDensity_component_eventuallyEq
    (A := A) hFg hHg 0).self_of_nhds
  norm_num only [canonicalCoefficientComponent] at hcomponent
  have hformula := (coordinatePrincipalDensity_radial_cylinder
    (A := A) (H := fun t => h (t, 0)) hY).1
  have hscalar : h ((G p).1, 0) ^ 2 /
      |deriv (fun t => (F (t, 0)).1) (G p).1| *
      (w (G p).1 * deriv (fun t => (F (t, 0)).1) (G p).1 ^ 2) = 1 := by
    have hn := hformula.symm.trans (hcomponent.symm.trans (hunit (G p) hp).1)
    simpa only [ha (G p) hp] using hn
  have hinverse := radial_unit_density_inverse_slope hscalar
  rw [inverseChartPotential_radial_formula_on_strip hF hshape hheight ha hb hp,
    div_eq_mul_inv, hinverse]
  ring

/-- This is the stored potential of the original actual negative half,
evaluated at its actual inverse point. No replacement chart, height or
operator field is selected. -/
theorem n04Coordinates_actual_reference_negative_potential_formula
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S (n04bActualTypedAtlas hT hS hN hfield e)
      (e.symm (.inl (m, side)))) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := e.symm (.inl (m, side))
    let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
    let x := K.inverseChart z₀ k p
    let H := fun r : ℝ => K.height z₀ k (r, 0)
    K.potential z₀ k p = D.w x.1 * H x.1 ^ 3 *
      deriv (fun r => D.w r * deriv H r) x.1 := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  have hi : e k = .inl (m, side) := e.apply_symm_apply _
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hA : Blueprint.N04PartA D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hx : K.inverseChart z₀ k p ∈ physicalPieceOpen S K z₀ k :=
    (hA.charts z₀ href hsref k).2.1 hp
  have hxraw : K.inverseChart z₀ k p ∈
      n04bTypedPhysicalDomain (D := D) C (n04bActualTravelChart S C L z₀) (.inl (m, side)) := by
    simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen, hi] using hx
  have hxfull : K.inverseChart z₀ k p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    n04b_typed_negative_domain_subset (m, side) hxraw
  have hradial := n04Coordinates_actual_reference_negative_radial_fields
    hT hS hN hfield e m side
  have ha (q : PolarPoint) (_hq : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      (L.coefficients z₀).a q = D.w q.1 :=
    (hN.2.1 z₀ href hsref q).trans (hN.1.1.reference_coefficients q).1
  have hunit (q : PolarPoint) (hq : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      (coordinatePrincipalDensity (L.coefficients z₀) (K.chart z₀ k) (K.height z₀ k)).a q = 1 ∧
        (coordinatePrincipalDensity (L.coefficients z₀) (K.chart z₀ k) (K.height z₀ k)).b q = 0 := by
    have hd := n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e href hsref k m side hi hq
    exact ⟨hd.1, hd.2.1⟩
  have hnegative : K.positive k = false := by
    simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive, hi, n04TypedPiecePositive]
  have hstored : K.potential z₀ k p = (if K.positive k then -1 else (1 : ℝ)) *
      inverseChartPotential (L.coefficients z₀) (K.chart z₀ k)
        (K.inverseChart z₀ k) (K.height z₀ k) p := rfl
  have hpotential : K.potential z₀ k p =
      inverseChartPotential (L.coefficients z₀) (K.chart z₀ k)
        (K.inverseChart z₀ k) (K.height z₀ k) p := by
    simpa only [hnegative, Bool.false_eq_true, ite_false, one_mul] using hstored
  exact hpotential.trans
    (inverseChartPotential_radial_unit_formula_on_strip hradial.1 hradial.2.2.1
      hradial.2.2.2.1 ha hunit hxfull)

end ContinuousFlexibility.Analysis
