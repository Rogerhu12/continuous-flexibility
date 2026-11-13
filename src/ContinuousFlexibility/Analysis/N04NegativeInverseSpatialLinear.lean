import ContinuousFlexibility.Analysis.N04NegativeInverseImplicitIdentification
import ContinuousFlexibility.Analysis.PlanarInverseDerivativeBound

/-!
# The actual spatial inverse used in the mixed inverse recursion

The inverse operator is extracted from the genuine forward spatial
differential. Its continuity follows in the original parameter topology.
In dimension two its norm is bounded by forward first spatial jets and
the reciprocal actual Jacobian, with no inverse derivative estimate
among the hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The planar linear inverse is controlled by its forward columns and
the reciprocal determinant. The existing inverse-germ formula is
applied to the linear maps themselves. -/
theorem n04NegativeInverse_clm_inverse_norm_le
    (D : PolarPoint →L[ℝ] PolarPoint) (hD : D.det ≠ 0)
    {M I : ℝ} (hM : 0 ≤ M) (hI : |D.det|⁻¹ ≤ I)
    (hcolumns : ∀ v : PolarPoint, ‖v‖ ≤ 1 → ‖D v‖ ≤ M) :
    ‖D.inverse‖ ≤ 2 * M * I := by
  let e : PolarPoint ≃L[ℝ] PolarPoint := D.toContinuousLinearEquivOfDetNeZero hD
  have hInv : D.IsInvertible :=
    ⟨e, by simp only [e, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]⟩
  have hgerm : (D.inverse : PolarPoint → PolarPoint) ∘ (D : PolarPoint → PolarPoint) =ᶠ[𝓝 0]
      (id : PolarPoint → PolarPoint) :=
    Filter.Eventually.of_forall (fun v => hInv.inverse_apply_self v)
  have hderiv : fderiv ℝ (D : PolarPoint → PolarPoint) 0 = D := D.hasFDerivAt.fderiv
  have hideriv : fderiv ℝ (D.inverse : PolarPoint → PolarPoint) (D 0) = D.inverse :=
    D.inverse.hasFDerivAt.fderiv
  have hdet : planeJacobian (D : PolarPoint → PolarPoint) 0 = D.det := by
    rw [planeJacobian_eq_fderiv_det, hderiv]
  have hr := hcolumns (1, 0) (by norm_num [Prod.norm_def])
  have ht := hcolumns (0, 1) (by norm_num [Prod.norm_def])
  have h11 : |(fderiv ℝ (D : PolarPoint → PolarPoint) 0 (1, 0)).1| ≤ M := by
    rw [hderiv]
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hr
  have h12 : |(fderiv ℝ (D : PolarPoint → PolarPoint) 0 (0, 1)).1| ≤ M := by
    rw [hderiv]
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans ht
  have h21 : |(fderiv ℝ (D : PolarPoint → PolarPoint) 0 (1, 0)).2| ≤ M := by
    rw [hderiv]
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hr
  have h22 : |(fderiv ℝ (D : PolarPoint → PolarPoint) 0 (0, 1)).2| ≤ M := by
    rw [hderiv]
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans ht
  have hnorm := fderiv_inverse_norm_le_of_germ D.differentiableAt D.inverse.differentiableAt
    hgerm (abs_pos.mpr hD) (by rw [hdet]) h11 h12 h21 h22
  rw [hideriv] at hnorm
  exact hnorm.trans (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num) hM))

namespace N04NegativeInverseJet

section Generic

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V W : Set Y} {F G : E × Y → Y}

def spatialInverse (J : SmoothDirections (U ×ˢ V) F) (G : E × Y → Y)
    (p : E × Y) : Y →L[ℝ] Y :=
  (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)).inverse

theorem spatialInverse_continuousOn (J : SmoothDirections (U ×ˢ V) F)
    (hG : ContinuousOn G (U ×ˢ W)) (hmap : MapsTo G (U ×ˢ W) V)
    (hD : ∀ p ∈ U ×ˢ W,
      (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)).IsInvertible) :
    ContinuousOn (spatialInverse J G) (U ×ˢ W) := by
  have hDc : ContinuousOn
      (fun p : E × Y => N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p))
      (U ×ˢ W) :=
    (N04NegativeGeometryImplicitJet.spatialDifferential_continuousOn J).comp
      (continuous_fst.continuousOn.prodMk hG) (fun p hp => ⟨hp.1, hmap hp⟩)
  intro p hp
  exact ((hD p hp).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
    (hDc p hp)

theorem spatialInverse_left (J : SmoothDirections (U ×ˢ V) F)
    (p : E × Y)
    (hD : (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)).IsInvertible)
    (y : Y) :
    spatialInverse J G p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y := by
  rw [← N04NegativeGeometryImplicitJet.spatialDifferential_apply]
  exact hD.inverse_apply_self y

end Generic

section Planar

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V W : Set PolarPoint} {F G : E × PolarPoint → PolarPoint}

theorem spatialDifferential_det (J : SmoothDirections (U ×ˢ V) F)
    (p : E × PolarPoint) (hp : (p.1, G p) ∈ U ×ˢ V) :
    (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)).det =
      planeJacobian (fun y => F (p.1, y)) (G p) := by
  rw [N04NegativeGeometryImplicitJet.spatialDifferential_eq_fderiv J _ hp,
    planeJacobian_eq_fderiv_det]

theorem spatialDifferential_isInvertible (J : SmoothDirections (U ×ˢ V) F)
    (p : E × PolarPoint) (hp : (p.1, G p) ∈ U ×ˢ V)
    (hJac : planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0) :
    (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)).IsInvertible := by
  let D := N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p)
  have hd : D.det ≠ 0 := by rw [spatialDifferential_det J p hp]; exact hJac
  let e : PolarPoint ≃L[ℝ] PolarPoint := D.toContinuousLinearEquivOfDetNeZero hd
  exact ⟨e, by simp only [e, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]⟩

theorem spatialInverse_continuousOn_of_jacobian (J : SmoothDirections (U ×ˢ V) F)
    (hG : ContinuousOn G (U ×ˢ W)) (hmap : MapsTo G (U ×ˢ W) V)
    (hJac : ∀ p ∈ U ×ˢ W, planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0) :
    ContinuousOn (spatialInverse J G) (U ×ˢ W) :=
  spatialInverse_continuousOn J hG hmap
    (fun p hp => spatialDifferential_isInvertible J p ⟨hp.1, hmap hp⟩ (hJac p hp))

theorem spatialInverse_left_of_jacobian (J : SmoothDirections (U ×ˢ V) F)
    (p : E × PolarPoint) (hp : (p.1, G p) ∈ U ×ˢ V)
    (hJac : planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0) (y : PolarPoint) :
    spatialInverse J G p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y :=
  spatialInverse_left J p (spatialDifferential_isInvertible J p hp hJac) y

/-- The only quantitative inputs for the operator in the true inverse
recurrence are the actual forward first spatial columns and the actual
Jacobian reciprocal at the actual inverse point. -/
theorem spatialInverse_norm_le (J : SmoothDirections (U ×ˢ V) F)
    (p : E × PolarPoint) (hp : (p.1, G p) ∈ U ×ˢ V)
    (hJac : planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0)
    {M I : ℝ} (hM : 0 ≤ M)
    (hI : |planeJacobian (fun y => F (p.1, y)) (G p)|⁻¹ ≤ I)
    (hforward : ∀ y : PolarPoint, ‖y‖ ≤ 1 →
      ‖J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))‖ ≤ M) :
    ‖spatialInverse J G p‖ ≤ 2 * M * I := by
  apply n04NegativeInverse_clm_inverse_norm_le
    (N04NegativeGeometryImplicitJet.spatialDifferential J (p.1, G p))
  · rw [spatialDifferential_det J p hp]
    exact hJac
  · exact hM
  · rw [spatialDifferential_det J p hp]
    exact hI
  · intro y hy
    rw [N04NegativeGeometryImplicitJet.spatialDifferential_apply]
    exact hforward y hy

end Planar
end N04NegativeInverseJet
end ContinuousFlexibility.Analysis
