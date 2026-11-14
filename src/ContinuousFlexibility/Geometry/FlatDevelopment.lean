module

public import ContinuousFlexibility.Geometry.HeightCoframe
public import ContinuousFlexibility.Geometry.Primitive
public import ContinuousFlexibility.Geometry.LocalInverse

/-!
# Actual local planar development of a zero-residual height

On an open convex positive-radius coordinate domain, two applications of
Poincare's lemma produce a genuinely smooth development. The derivative
preserves the explicitly specified Euclidean coordinate quadratic form.

This does not assert global exactness of the polar connection on an annulus:
its period there can be `2π`. Global filled-disk reconstruction additionally
requires the Cartesian coframe, the angle gauge, and global injectivity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Smoothness of the actual connection coefficients on the positive domain. -/
theorem contDiffAt_heightConnection
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hz : ContDiffAt ℝ ∞ z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    ContDiffAt ℝ ∞ (heightConnectionForm w z).radial x ∧
      ContDiffAt ℝ ∞ (heightConnectionForm w z).angular x := by
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) x :=
    contDiffAt_const.add ((hw.comp x contDiffAt_fst).pow 2)
  have hk : ContDiffAt ℝ ∞ (heightRadial z) x :=
    contDiffAt_heightRadial hz (by simp)
  have hp : ContDiffAt ℝ ∞ (heightAngular z) x :=
    contDiffAt_heightAngular hz (by simp) hr
  have hcp : ContDiffAt ℝ ∞ (fun y => 1 - heightAngular z y ^ 2) x :=
    contDiffAt_const.sub (hp.pow 2)
  have hd := (hE.mul hcp).sub (hk.pow 2)
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  have hsD := hd.sqrt hD.ne'
  have hB : ContDiffAt ℝ ∞
      (fun y => connectionB1 (profileEnergy w y) (heightRadial z y) (heightAngular z y)) x :=
    hk.div (hcp.mul hsD) (mul_ne_zero hc.ne' (Real.sqrt_pos.mpr hD).ne')
  have hF : ContDiffAt ℝ ∞
      (fun y => connectionInverseRoot (profileEnergy w y) (heightRadial z y) (heightAngular z y)) x :=
    contDiffAt_const.div hsD (Real.sqrt_pos.mpr hD).ne'
  have hpr : ContDiffAt ℝ ∞ (radialPartial (heightAngular z)) x :=
    contDiffAt_radialPartial hp (by simp)
  have hpt : ContDiffAt ℝ ∞ (angularPartial (heightAngular z)) x :=
    contDiffAt_angularPartial hp (by simp)
  exact ⟨hB.mul hpr, hF.add (hB.mul hpt)⟩

theorem contDiffAt_heightCoframe
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hz : ContDiffAt ℝ ∞ z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    ContDiffAt ℝ ∞ (heightCoframeOne w z).radial x ∧
      ContDiffAt ℝ ∞ (heightCoframeOne w z).angular x ∧
      ContDiffAt ℝ ∞ (heightCoframeTwo w z).radial x ∧
      ContDiffAt ℝ ∞ (heightCoframeTwo w z).angular x := by
  exact ⟨contDiffAt_heightCoframeOne_radial hw (by simpa using hz) hr hD,
    contDiffAt_const,
    contDiffAt_heightCoframeTwo_radial (by simpa using hz) hr hD,
    contDiffAt_heightCoframeTwo_angular (by simpa using hz) hr hD⟩

/-- A zero of the genuine height residual gives an actual smooth planar
development on each open convex positive-radius coordinate domain. -/
theorem exists_smooth_remainder_development
    {U : Set PolarPoint} {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hw : ∀ x ∈ U, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ U, 0 < x.1)
    (hD : ∀ x ∈ U, 0 < polarDiscriminant w z x)
    (hres : ∀ x ∈ U, polarCoordinateResidual w z x = 0) :
    ∃ P : PolarPoint → PolarPoint,
      (∀ x ∈ U, ContDiffAt ℝ ∞ P x) ∧
        ∀ x ∈ U, ∀ v : PolarPoint,
          (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
            remainderQuadratic x.1 (profileEnergy w x) (heightRadial z x)
              (heightAngular z x) v.1 v.2 := by
  let α := heightConnectionForm w z
  let η₁ := heightCoframeOne w z
  let η₂ := heightCoframeTwo w z
  have hα : ∀ x ∈ U, ContDiffAt ℝ ∞ α.radial x ∧ ContDiffAt ℝ ∞ α.angular x := by
    intro x hx
    exact contDiffAt_heightConnection (hw x hx) (hz x hx) (hr x hx).ne' (hD x hx)
  have hη : ∀ x ∈ U, ContDiffAt ℝ ∞ η₁.radial x ∧ ContDiffAt ℝ ∞ η₁.angular x ∧
      ContDiffAt ℝ ∞ η₂.radial x ∧ ContDiffAt ℝ ∞ η₂.angular x := by
    intro x hx
    exact contDiffAt_heightCoframe (hw x hx) (hz x hx) (hr x hx).ne' (hD x hx)
  have hαclosed : ∀ x ∈ U, exteriorCoefficient α x = 0 := by
    intro x hx
    exact heightConnection_closed_of_residual_zero
      ((hw x hx).differentiableAt (by simp)) ((hz x hx).of_le (by simp))
      (hr x hx).ne' (hD x hx) (hres x hx)
  obtain ⟨ψ, hψ⟩ := exists_primitive_of_closed hU hUo
    (fun x hx => (hα x hx).1.differentiableAt (by simp))
    (fun x hx => (hα x hx).2.differentiableAt (by simp)) hαclosed
  have hψs : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x := by
    intro x hx
    exact contDiffAt_of_primitive_infty hUo hx hψ (hα x hx).1 (hα x hx).2
  let ξ₁ := rotatedCoframeOne ψ η₁ η₂
  let ξ₂ := rotatedCoframeTwo ψ η₁ η₂
  have hξ : ∀ x ∈ U, ContDiffAt ℝ ∞ ξ₁.radial x ∧ ContDiffAt ℝ ∞ ξ₁.angular x ∧
      ContDiffAt ℝ ∞ ξ₂.radial x ∧ ContDiffAt ℝ ∞ ξ₂.angular x := by
    intro x hx
    obtain ⟨h1r, h1t, h2r, h2t⟩ := hη x hx
    exact ⟨contDiffAt_rotatedCoframeOne_radial (hψs x hx) h1r h2r,
      contDiffAt_rotatedCoframeOne_angular (hψs x hx) h1t h2t,
      contDiffAt_rotatedCoframeTwo_radial (hψs x hx) h1r h2r,
      contDiffAt_rotatedCoframeTwo_angular (hψs x hx) h1t h2t⟩
  have hξclosed : ∀ x ∈ U, exteriorCoefficient ξ₁ x = 0 ∧ exteriorCoefficient ξ₂ x = 0 := by
    intro x hx
    have hψr : radialPartial ψ x = α.radial x := by
      unfold radialPartial
      rw [(hψ x hx).fderiv]
      simp [PlaneOneForm.toCLM_apply, formValue]
    have hψt : angularPartial ψ x = α.angular x := by
      unfold angularPartial
      rw [(hψ x hx).fderiv]
      simp [PlaneOneForm.toCLM_apply, formValue]
    exact height_rotatedCoframe_closed ((hw x hx).differentiableAt (by simp))
      ((hz x hx).of_le (by simp)) (hr x hx).ne' (hD x hx)
      (hψ x hx).differentiableAt hψr hψt
  obtain ⟨P, hP, hPs⟩ := exists_smooth_development_of_closed_coframe hU hUo
    (fun x hx => (hξ x hx).1) (fun x hx => (hξ x hx).2.1)
    (fun x hx => (hξ x hx).2.2.1) (fun x hx => (hξ x hx).2.2.2)
    (fun x hx => (hξclosed x hx).1) (fun x hx => (hξclosed x hx).2)
  refine ⟨P, hPs, ?_⟩
  intro x hx v
  rw [development_derivative_square_sum (hP x hx) v]
  change formValue (rotatedCoframeOne ψ η₁ η₂) x v ^ 2 +
    formValue (rotatedCoframeTwo ψ η₁ η₂) x v ^ 2 = _
  rw [rotatedCoframe_square_sum]
  exact heightCoframe_square_sum (hD x hx) v

/-- The smooth development has a genuine smooth local inverse at every point.
No global injectivity on an annulus or a disk is asserted here. -/
theorem exists_locally_invertible_remainder_development
    {U : Set PolarPoint} {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hw : ∀ x ∈ U, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ U, 0 < x.1)
    (hD : ∀ x ∈ U, 0 < polarDiscriminant w z x)
    (hres : ∀ x ∈ U, polarCoordinateResidual w z x = 0) :
    ∃ P : PolarPoint → PolarPoint,
      (∀ x ∈ U, ContDiffAt ℝ ∞ P x) ∧
      (∀ x ∈ U, ∀ v : PolarPoint,
        (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
          remainderQuadratic x.1 (profileEnergy w x) (heightRadial z x)
            (heightAngular z x) v.1 v.2) ∧
      ∀ x ∈ U, ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
        (e : PolarPoint → PolarPoint) = P ∧ x ∈ e.source ∧ P x ∈ e.target ∧
          ContDiffAt ℝ ∞ e.symm (P x) := by
  obtain ⟨P, hPs, hmetric⟩ := exists_smooth_remainder_development hU hUo hw hz hr hD hres
  refine ⟨P, hPs, hmetric, ?_⟩
  intro x hx
  exact exists_smooth_localInverse_of_remainder_metric (hPs x hx) (hr x hx)
    (radialEnergy_pos (w x.1)) (hD x hx) (hmetric x hx)

/-- The Euclidean bilinear form in explicit planar coordinates. It is not
the bilinear form of the default max-norm on `PolarPoint`. -/
def coordinateEuclideanPair (u v : PolarPoint) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The actual symmetric coordinate tensor `g - dz ⊗ dz`. -/
def remainderBilinear (r E k p : ℝ) (u v : PolarPoint) : ℝ :=
  (E - k ^ 2) * u.1 * v.1 - r * k * p * (u.1 * v.2 + u.2 * v.1) +
    r ^ 2 * (1 - p ^ 2) * u.2 * v.2

/-- Polarization turns the proved quadratic identity into the full pullback
bilinear identity on every pair of tangent vectors. -/
theorem coordinate_pair_eq_remainder_of_square_sum
    (L : PolarPoint →L[ℝ] PolarPoint) (r E k p : ℝ)
    (hmetric : ∀ v : PolarPoint,
      (L v).1 ^ 2 + (L v).2 ^ 2 = remainderQuadratic r E k p v.1 v.2)
    (u v : PolarPoint) :
    coordinateEuclideanPair (L u) (L v) = remainderBilinear r E k p u v := by
  have hu := hmetric u
  have hv := hmetric v
  have huv := hmetric (u + v)
  simp only [map_add, Prod.fst_add, Prod.snd_add] at huv
  unfold remainderQuadratic at hu hv huv
  unfold coordinateEuclideanPair remainderBilinear
  nlinarith

theorem development_pullback_bilinear
    {P : PolarPoint → PolarPoint} {x : PolarPoint} {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic x.1 (profileEnergy w x) (heightRadial z x)
          (heightAngular z x) v.1 v.2) (u v : PolarPoint) :
    coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) =
      remainderBilinear x.1 (profileEnergy w x) (heightRadial z x) (heightAngular z x) u v :=
  coordinate_pair_eq_remainder_of_square_sum (fderiv ℝ P x) _ _ _ _ hmetric u v

end ContinuousFlexibility
