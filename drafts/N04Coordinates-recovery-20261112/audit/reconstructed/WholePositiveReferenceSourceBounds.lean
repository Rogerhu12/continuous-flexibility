import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# Absolute reference source factors on the actual whole positive pieces

The reference chart and its inverse are the identity and its height is one.
Consequently the source factor of this same atlas is exactly one. The three
absolute reference multipliers have a common zero-order bound on every
positive piece, independent of the component and the current state.
This does not assert the corresponding negative-piece estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeCanonicalAtlasData_positive_reference_source
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hFref : F (C.referenceState, 0) i = id)
    (hGref : G (C.referenceState, 0) i = id)
    (hQref : Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    canonicalReferencePoint C W z m = F z i ∧
      canonicalReferenceSourceFactor C W z m = (fun _ => (1 : ℝ)) := by
  constructor
  · funext p
    simp only [canonicalReferencePoint, n04WholeCanonicalAtlasData,
      n04bWithInteriorDivision, hi, hGref, id_eq]
  · funext p
    simp only [canonicalReferenceSourceFactor, n04WholeCanonicalAtlasData,
      n04bWithInteriorDivision, hi, wholePositiveChartHeight, hFref, hQref,
      inv_one, planeJacobian, fderiv_id, ContinuousLinearMap.id_apply,
      one_mul, zero_mul, sub_zero, abs_one, div_one]

/-- The bound is chosen before the state and component. The only geometric
input at a positive piece is the actual chart's already proved `MapsTo` law. -/
theorem n04WholeCanonicalAtlasData_positive_reference_source_bound
    (hD : RadialProfileGeometry D)
    (href : ∀ i, F (C.referenceState, 0) i = id ∧
      G (C.referenceState, 0) i = id ∧
      Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    ∃ B : ℝ, 0 < B ∧ ∀ (z : AnnularState S × ℝ) (m : ℕ)
      (i : N04PositiveComponent D.a D.b (deriv D.w)), e m = .inr i →
      MapsTo (F z i)
        (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ))
        (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) →
      ∀ x ∈ physicalPieceOpen S W z m, ∀ k : Fin 3,
        |canonicalPrimitiveField D T C W z m (.inr (.inr k)) x| ≤ B := by
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hdw : Continuous (deriv D.w) := hw.continuous_deriv (by simp)
  have hrnz (r : ℝ) (hr : r ∈ Icc D.a D.b) : r ≠ 0 :=
    (hD.1.trans_le hr.1).ne'
  let V : ℝ → ℝ × ℝ × ℝ := fun r => (deriv D.w r, D.w r, deriv D.w r / r)
  have hV : ContinuousOn V (Icc D.a D.b) :=
    hdw.continuousOn.prodMk (hw.continuous.continuousOn.prodMk
      (hdw.continuousOn.div continuousOn_id hrnz))
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  let B : ℝ := max B₀ 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hvalues (r : ℝ) (hr : r ∈ Icc D.a D.b) :
      |deriv D.w r| ≤ B ∧ |D.w r| ≤ B ∧ |deriv D.w r / r| ≤ B := by
    have hb := (hB₀ r hr).trans (le_max_left B₀ 1)
    simpa only [V, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hb
  change ∃ B : ℝ, 0 < B ∧ ∀ z m i, e m = .inr i →
    MapsTo (F z i)
      (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ))
      (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) →
    ∀ x ∈ physicalPieceOpen S W z m, ∀ k : Fin 3,
      |canonicalPrimitiveField D T C W z m (.inr (.inr k)) x| ≤ B
  refine ⟨B, hB, ?_⟩
  intro z m i hi hmap x hx k
  rcases n04WholeCanonicalAtlasData_positive_fields C L K e cell F G Q N z m i hi with
    ⟨_, _, _, _, hdomain, _, _, _, _, _, _, _⟩
  have hx' : x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) := by
    rwa [hdomain] at hx
  have himage := hmap hx'
  have hcore := n04PositiveComponent_interval_subset hdw i himage.1
  have hv := hvalues (F z i x).1 ⟨hcore.1.le, hcore.2.le⟩
  have hsource := n04WholeCanonicalAtlasData_positive_reference_source
    C L K e cell F G Q N z m i hi (href i).1 (href i).2.1 (href i).2.2
  simp only [canonicalPrimitiveField, hsource.1, hsource.2, one_mul]
  split_ifs with hzero hone
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2

end ContinuousFlexibility.Analysis
