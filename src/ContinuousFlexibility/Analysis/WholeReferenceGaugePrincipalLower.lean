module

public import ContinuousFlexibility.Analysis.PositiveReferencePhysicalLower
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeReferencePrincipal

/-!
# Physical inputs for the actual reference angular lower bound

All maps and heights below are the same chosen Y and H used by the new
whole atlas. The profile lower bound is stated on the physical positive
component. The final criterion records the precise uniform cost that
the profile and interpolation estimates must supply; it does not assert
that these estimates follow from the current Through03 hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

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

theorem n04WholeReferenceGaugeAtlasData_positive_reference_lower_of_profile
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    {h k M : ℝ} (hh : 0 < h) (hk : 0 < k) (hM : 0 < M)
    (hheight : ∀ r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i), h ≤ H i r)
    (hslope : ∀ r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i), deriv (Y i) r ≤ M)
    (hprofile : ∀ r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i),
      k * min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤ deriv D.w r / r)
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
    (h ^ 2 * k / M ^ 2) * (p.1 * (1 - p.1)) ≤
      (V.coefficients (C.referenceState, 0) m).c p := by
  let x : PolarPoint := positiveReferenceCylinderInverse (Y i) p
  have hfields := n04WholeReferenceGaugeAtlasData_positive_fields
    C L (n04bActualTypedAtlas hT hS hN hfield e₀) e cell
    (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j (q : PolarPoint) => H j q.1) τ σ Q N (C.referenceState, 0) m i hi
  have hp01 : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    simpa only [canonicalOpen, hfields.1, hfields.2.1] using hp
  have hx : x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) :=
    hgeometry.inverse_maps_open hp01
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ (Y i) := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hgeometry.chart_smooth.fst.comp hline
  have hYpos : 0 < deriv (Y i) x.1 := by
    simpa only [planeJacobian_positiveReferenceCylinderChart
      (hY.differentiable (by simp) x.1)] using hgeometry.jacobian_positive x
  have hend := PositiveChartRangeGeometry.cylinder_endpoint_values
    (hx.1.1.trans hx.1.2) hgeometry
  have hYx : Y i x.1 = p.1 := congrArg Prod.fst (hgeometry.right_inverse p)
  have hYr : Y i x.1 ∈ Icc (0 : ℝ) 1 := by
    rw [hYx]
    exact ⟨hp01.1.1.le, hp01.1.2.le⟩
  have hlower := radial_reference_c_lower_of_physical_profile
    hY.continuous.continuousOn (hY.differentiable (by simp)).differentiableOn
    hslope hend.1 hend.2 hx.1 hYr hM hh.le (hheight x.1 hx.1) hk.le hYpos
    (hprofile x.1 hx.1)
  have hc := (n04WholeReferenceGaugeAtlasData_positive_reference_formulas
    hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi hgeometry href hp).2.2.1
  have hlower' : (h ^ 2 * k / M ^ 2) * (p.1 * (1 - p.1)) ≤
      H i x.1 ^ 2 / deriv (Y i) x.1 * (deriv D.w x.1 / x.1) := by
    simpa only [hYx] using hlower
  exact hlower'.trans_eq hc.symm

/-- This is a physical-input criterion, not an unconditional construction
of the uniform lower bound. The cost is formed from the actual height
lower bound, the actual chart derivative upper bound, and the physical
profile's linear endpoint lower bound on each same component. -/
theorem n04WholeReferenceGaugeAtlasData_referencePrincipal_of_physical_costs
    {newBase : ℕ} {ε' : ℝ} (hε' : 0 < ε')
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N) newBase ε')
    (h k M : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hbounds : ∀ i, 0 < h i ∧ 0 < k i ∧ 0 < M i ∧
      ∀ r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i),
        h i ≤ H i r ∧ deriv (Y i) r ≤ M i ∧
          k i * min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤ deriv D.w r / r)
    {B : ℝ} (hB : 0 < B)
    (hcost : ∀ i, M i ^ 2 ≤ (B * T.E0 (T.sample (cell i)) ^ B) * (h i ^ 2 * k i)) :
    CanonicalGeometry.ReferencePrincipal T S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  refine ⟨n04WholeReferenceGaugeAtlasData_actual_referencePrincipal_qualitative
    hT hS hN hfield e₀ e cell Y H τ σ Q N hε' href hgeometry hA, B, hB, ?_⟩
  intro m hm p hp
  cases hi : e m with
  | inl j =>
      have hneg : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hneg.symm.trans hm))
  | inr i =>
      obtain ⟨hh, hk, hM, hb⟩ := hbounds i
      have hlower := n04WholeReferenceGaugeAtlasData_positive_reference_lower_of_profile
        hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi (hgeometry i) (href i)
        hh hk hM (fun r hr => (hb r hr).1) (fun r hr => (hb r hr).2.1)
        (fun r hr => (hb r hr).2.2) hp
      obtain ⟨hl, hr, _, _, _, hcell, _, _, _, _, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_fields
          C L (n04bActualTypedAtlas hT hS hN hfield e₀) e cell
          (fun i => positiveReferenceCylinderChart (Y i))
          (fun i => positiveReferenceCylinderInverse (Y i))
          (fun i (p : PolarPoint) => H i p.1) τ σ Q N (C.referenceState, 0) m i hi
      have hp01 : p.1 ∈ Ioo (0 : ℝ) 1 := by
        simpa only [canonicalOpen, hl, hr] using hp.1
      let cost := B * T.E0 (T.sample (cell i)) ^ B
      have hcost' : M i ^ 2 ≤ cost * (h i ^ 2 * k i) := hcost i
      have hpos : 0 < h i ^ 2 * k i := mul_pos (sq_pos_of_pos hh) hk
      have hcostpos : 0 < cost := by
        by_contra hn
        have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hpos.le
        exact (not_lt_of_ge (hcost'.trans hnonpos)) (sq_pos_of_pos hM)
      have hconstant : cost⁻¹ ≤ h i ^ 2 * k i / M i ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hM)).2
        have hd : M i ^ 2 / cost ≤ h i ^ 2 * k i :=
          (div_le_iff₀ hcostpos).2 (by simpa only [mul_comm] using hcost')
        simpa only [div_eq_mul_inv, mul_comm] using hd
      have hnonneg : 0 ≤ p.1 * (1 - p.1) :=
        mul_nonneg hp01.1.le (sub_nonneg.mpr hp01.2.le)
      simpa only [cost, hl, hr, hcell, sub_zero] using
        (mul_le_mul_of_nonneg_right hconstant hnonneg).trans hlower

end ContinuousFlexibility.Analysis
