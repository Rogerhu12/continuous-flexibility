import ContinuousFlexibility.Analysis.RadialReferencePrincipalFormulas
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasOperator
import ContinuousFlexibility.Analysis.WholeReferenceGaugeRelativeFields
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity

/-!
# Actual positive reference principal fields in the new whole atlas

The same constructed scalar reference chart and height determine all
three principal coefficients and the potential. Their formulas give
strict positivity and radiality on each positive canonical piece. The
uniform material lower bound for the angular coefficient is a separate
quantitative obligation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04Coordinates_reference_positive_coefficient_germs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hpos : 0 < deriv D.w p.1) :
    (L.coefficients (C.referenceState, 0)).a =ᶠ[𝓝 p]
        (fun q : PolarPoint => D.w q.1) ∧
      (L.coefficients (C.referenceState, 0)).b =ᶠ[𝓝 p]
        (fun _ : PolarPoint => (0 : ℝ)) ∧
      (L.coefficients (C.referenceState, 0)).c =ᶠ[𝓝 p]
        (fun q : PolarPoint => deriv D.w q.1 / q.1) := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  have hbc := hN.2.2.1 (C.referenceState, 0) hz hs p hp hpos
  refine ⟨Filter.Eventually.of_forall ?_, hbc.1.trans ?_, hbc.2.trans ?_⟩
  · intro q
    exact (hN.2.1 (C.referenceState, 0) hz hs q).trans
      (hN.1.1.reference_coefficients q).1
  · exact Filter.Eventually.of_forall (fun q => (hN.1.1.reference_coefficients q).2.1)
  · exact Filter.Eventually.of_forall (fun q => (hN.1.1.reference_coefficients q).2.2)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGaugeAtlasData_positive_reference_formulas
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    {p : PolarPoint}
    (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j q => H j q.1) τ σ Q N) m) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j q => H j q.1) τ σ Q N
    let A := V.coefficients (C.referenceState, 0) m
    let r := Function.invFun (Y i) p.1
    A.a p = H i r ^ 2 * D.w r * deriv (Y i) r ∧ A.b p = 0 ∧
      A.c p = H i r ^ 2 / deriv (Y i) r * (deriv D.w r / r) ∧
      V.potential (C.referenceState, 0) m p =
        -(H i r * deriv (fun t => D.w t * deriv (H i) t) r / deriv (Y i) r) ∧
      0 < A.a p ∧ 0 < A.c p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun j => positiveReferenceCylinderChart (Y j)
  let χ := fun j => positiveReferenceCylinderInverse (Y j)
  let h₀ := fun j (q : PolarPoint) => H j q.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let x : PolarPoint := positiveReferenceCylinderInverse (Y i) p
  have hD : RadialProfileGeometry D := n04b_profileGeometry_of_through03 hN
  have hdw : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨hl, hr, _, _, _, _, hpositive, _, _, _, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
      z₀ m i hi
  have hp01 : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    have hp' : p ∈ Ioo (V.left m) (V.right m) ×ˢ (univ : Set ℝ) := hp
    rw [show V.left m = 0 from hl, show V.right m = 1 from hr] at hp'
    exact hp'
  have hx := hgeometry.inverse_maps_open hp01
  have hxD : x ∈ annularOpen D :=
    ⟨n04PositiveComponent_interval_subset hdw i hx.1, mem_univ _⟩
  have hxpos : 0 < deriv D.w x.1 := n04PositiveComponent_interval_pos hdw i hx.1
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ (Y i) := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hgeometry.chart_smooth.fst.comp hline
  have hH : ContDiff ℝ ∞ (H i) := by
    simpa only [Function.comp_def] using hgeometry.height_smooth.comp hline
  have hYd : DifferentiableAt ℝ (Y i) x.1 := hY.differentiable (by simp) x.1
  have hYpos : 0 < deriv (Y i) x.1 := by
    simpa only [planeJacobian_positiveReferenceCylinderChart hYd] using
      hgeometry.jacobian_positive x
  have hHpos : 0 < H i x.1 := hgeometry.height_positive x
  have hwpos : 0 < D.w x.1 := hD.2.2.2.2.1 x.1 hxD.1
  have hrpos : 0 < x.1 := hD.1.trans hxD.1.1
  have hg := n04Coordinates_reference_positive_coefficient_germs hN hxD hxpos
  obtain ⟨hF, hG, hh⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_reference_fields C L K e cell ψ χ h₀
      τ σ Q N m i hi href.1 href.2.1 href.2.2
  have hf := n04WholeReferenceGaugeAtlasData_actual_operatorFields hT hS hN hfield
    e₀ e cell ψ χ h₀ τ σ Q N z₀ m
  have hcoeff : V.coefficients z₀ m =
      inverseChartPrincipalCoefficients (L.coefficients z₀)
        (positiveReferenceCylinderChart (Y i))
        (positiveReferenceCylinderInverse (Y i)) (fun q : PolarPoint => H i q.1) := by
    have h := hf.1
    change V.coefficients z₀ m = inverseChartPrincipalCoefficients (L.coefficients z₀)
      (V.chart z₀ m) (V.inverseChart z₀ m) (V.height z₀ m) at h
    rw [show V.chart z₀ m = ψ i from hF,
      show V.inverseChart z₀ m = χ i from hG,
      show V.height z₀ m = h₀ i from hh] at h
    exact h
  have hdensity := coordinatePrincipalDensity_radial_cylinder
    (A := L.coefficients z₀) (H := H i) hYd
  have ha : (V.coefficients z₀ m).a p = H i x.1 ^ 2 * D.w x.1 * deriv (Y i) x.1 := by
    rw [hcoeff]
    change (coordinatePrincipalDensity (L.coefficients z₀)
      (positiveReferenceCylinderChart (Y i)) (fun q : PolarPoint => H i q.1)).a x = _
    rw [hdensity.1, abs_of_pos hYpos, hg.1.self_of_nhds]
    field_simp [hYpos.ne']
    <;> ring
  have hb : (V.coefficients z₀ m).b p = 0 := by
    rw [hcoeff]
    change (coordinatePrincipalDensity (L.coefficients z₀)
      (positiveReferenceCylinderChart (Y i)) (fun q : PolarPoint => H i q.1)).b x = 0
    rw [hdensity.2.1, hg.2.1.self_of_nhds, zero_mul, mul_zero]
  have hc : (V.coefficients z₀ m).c p =
      H i x.1 ^ 2 / deriv (Y i) x.1 * (deriv D.w x.1 / x.1) := by
    rw [hcoeff]
    change (coordinatePrincipalDensity (L.coefficients z₀)
      (positiveReferenceCylinderChart (Y i)) (fun q : PolarPoint => H i q.1)).c x = _
    rw [hdensity.2.2, abs_of_pos hYpos, hg.2.2.self_of_nhds]
  have hv : V.potential z₀ m p =
      -(H i x.1 * deriv (fun t => D.w t * deriv (H i) t) x.1 / deriv (Y i) x.1) := by
    have hpot := hf.2 p
    rw [hpositive, hF, hG, hh] at hpot
    simp only [↓reduceIte, neg_one_mul] at hpot
    exact hpot.trans (congrArg Neg.neg
      (inverseChartPotential_radial_cylinder hD.2.2.1.1 hH hYd hYpos hg.1 hg.2.1))
  refine ⟨ha, hb, hc, hv, ?_, ?_⟩
  · rw [ha]
    exact mul_pos (mul_pos (sq_pos_of_pos hHpos) hwpos) hYpos
  · rw [hc]
    exact mul_pos (div_pos (sq_pos_of_pos hHpos) hYpos) (div_pos hxpos hrpos)

theorem n04WholeReferenceGaugeAtlasData_positive_reference_qualitative
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    {p : PolarPoint}
    (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j q => H j q.1) τ σ Q N) m) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j q => H j q.1) τ σ Q N
    let A := V.coefficients (C.referenceState, 0) m
    0 < A.a p ∧ A.b p = 0 ∧ A.a p = A.a (p.1, 0) ∧ A.c p = A.c (p.1, 0) ∧
      V.potential (C.referenceState, 0) m p = V.potential (C.referenceState, 0) m (p.1, 0) ∧
      0 < A.c p := by
  have hp₀ : (p.1, (0 : ℝ)) ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j q => H j q.1) τ σ Q N) m := ⟨hp.1, mem_univ _⟩
  obtain ⟨ha, hb, hc, hv, hapos, hcpos⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_reference_formulas hT hS hN hfield
      e₀ e cell Y H τ σ Q N m i hi hgeometry href hp
  obtain ⟨ha₀, _, hc₀, hv₀, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_reference_formulas hT hS hN hfield
      e₀ e cell Y H τ σ Q N m i hi hgeometry href hp₀
  exact ⟨hapos, hb, ha.trans ha₀.symm, hc.trans hc₀.symm, hv.trans hv₀.symm, hcpos⟩

end ContinuousFlexibility.Analysis
