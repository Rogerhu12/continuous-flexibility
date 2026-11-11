import ContinuousFlexibility.Geometry.CartesianCoframe
import ContinuousFlexibility.Geometry.GlobalCovering
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Whole-plane Cartesian development and exterior normalization

These constructions start with actual smooth one-forms on the whole
coordinate plane. A global primitive is produced by Poincare's lemma on
the convex plane, and constants are fixed on a connected open exterior.
No primitive of the polar connection on an annulus is assumed.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Genuine full-plane flat Cartan data. There is no development or primitive field. -/
structure FlatCartesianCoframe where
  connection : PlaneOneForm
  first : PlaneOneForm
  second : PlaneOneForm
  connection_smooth : ∀ x, ContDiffAt ℝ ∞ connection.radial x ∧
    ContDiffAt ℝ ∞ connection.angular x
  coframe_smooth : ∀ x, ContDiffAt ℝ ∞ first.radial x ∧
    ContDiffAt ℝ ∞ first.angular x ∧ ContDiffAt ℝ ∞ second.radial x ∧
    ContDiffAt ℝ ∞ second.angular x
  connection_closed : ∀ x, exteriorCoefficient connection x = 0
  cartan_first : ∀ x, exteriorCoefficient first x = wedgeCoefficient connection second x
  cartan_second : ∀ x, exteriorCoefficient second x = -wedgeCoefficient connection first x
  wedge_ne_zero : ∀ x, wedgeCoefficient first second x ≠ 0

theorem exists_global_smooth_primitive {α : PlaneOneForm}
    (hr : ∀ x, ContDiffAt ℝ ∞ α.radial x)
    (hθ : ∀ x, ContDiffAt ℝ ∞ α.angular x)
    (hc : ∀ x, exteriorCoefficient α x = 0) :
    ∃ ψ : PolarPoint → ℝ,
      (∀ x, HasFDerivAt ψ (α.toCLM x) x) ∧ ∀ x, ContDiffAt ℝ ∞ ψ x := by
  obtain ⟨ψ, hψ⟩ := exists_primitive_of_closed (U := Set.univ) convex_univ isOpen_univ
    (fun x _ => (hr x).differentiableAt (by simp))
    (fun x _ => (hθ x).differentiableAt (by simp)) (fun x _ => hc x)
  refine ⟨ψ, fun x => hψ x (mem_univ x), ?_⟩
  intro x
  exact contDiffAt_of_primitive_infty isOpen_univ (mem_univ x) hψ (hr x) (hθ x)

/-- The genuine primitive of a closed connection can be chosen to vanish on a connected open
exterior where that connection is zero. -/
theorem exists_global_smooth_primitive_zero_on_exterior
    {α : PlaneOneForm} {U : Set PolarPoint}
    (hr : ∀ x, ContDiffAt ℝ ∞ α.radial x)
    (hθ : ∀ x, ContDiffAt ℝ ∞ α.angular x)
    (hc : ∀ x, exteriorCoefficient α x = 0)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hzero : ∀ x ∈ U, α.radial x = 0 ∧ α.angular x = 0) :
    ∃ ψ : PolarPoint → ℝ,
      (∀ x, HasFDerivAt ψ (α.toCLM x) x) ∧
      (∀ x, ContDiffAt ℝ ∞ ψ x) ∧ Set.EqOn ψ 0 U := by
  obtain ⟨ψ, hψ, hψs⟩ := exists_global_smooth_primitive hr hθ hc
  have hd0 : U.EqOn (fderiv ℝ ψ) 0 := by
    intro x hx
    rw [(hψ x).fderiv]
    exact PlaneOneForm.toCLM_eq_zero_of_components (hzero x hx).1 (hzero x hx).2
  obtain ⟨c, hconst⟩ := hUo.exists_is_const_of_fderiv_eq_zero hUc
    (fun x _ => (hψ x).differentiableAt.differentiableWithinAt) hd0
  refine ⟨fun x => ψ x - c, fun x => (hψ x).sub_const c,
    fun x => (hψs x).sub contDiffAt_const, ?_⟩
  intro x hx
  change ψ x - c = 0
  rw [hconst x hx, sub_self]

/-- Derivative identity on a connected open exterior permits one global translation to
normalize the map to the identity there. -/
theorem exists_normalized_map_of_fderiv_eq_id_on_exterior
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hP : ∀ x, ContDiffAt ℝ ∞ P x)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hd : ∀ x ∈ U, fderiv ℝ P x = ContinuousLinearMap.id ℝ PolarPoint) :
    ∃ Q : PolarPoint → PolarPoint,
      (∀ x, ContDiffAt ℝ ∞ Q x) ∧
      (∀ x, fderiv ℝ Q x = fderiv ℝ P x) ∧ Set.EqOn Q id U := by
  obtain ⟨c, hc⟩ := hUo.exists_eq_add_of_fderiv_eq hUc
    (fun x _ => ((hP x).differentiableAt (by simp)).differentiableWithinAt)
    (differentiableOn_id : DifferentiableOn ℝ (id : PolarPoint → PolarPoint) U)
    (fun x hx => by rw [hd x hx, fderiv_id])
  refine ⟨fun x => P x - c, fun x => (hP x).sub contDiffAt_const,
    fun x => fderiv_sub_const c, ?_⟩
  intro x hx
  change P x - c = x
  rw [hc hx]
  exact add_sub_cancel_right x c

/-- Closed smooth Cartesian coframes have a genuine smooth development normalized to the
identity on a connected exterior on which the coframe is standard. -/
theorem exists_normalized_development_of_closed_cartesian_coframe
    {η₁ η₂ : PlaneOneForm} {U : Set PolarPoint}
    (h1r : ∀ x, ContDiffAt ℝ ∞ η₁.radial x)
    (h1θ : ∀ x, ContDiffAt ℝ ∞ η₁.angular x)
    (h2r : ∀ x, ContDiffAt ℝ ∞ η₂.radial x)
    (h2θ : ∀ x, ContDiffAt ℝ ∞ η₂.angular x)
    (hc1 : ∀ x, exteriorCoefficient η₁ x = 0)
    (hc2 : ∀ x, exteriorCoefficient η₂ x = 0)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hstd : ∀ x ∈ U, η₁.radial x = 1 ∧ η₁.angular x = 0 ∧
      η₂.radial x = 0 ∧ η₂.angular x = 1) :
    ∃ P : PolarPoint → PolarPoint,
      (∀ x, ContDiffAt ℝ ∞ P x) ∧
      (∀ x, HasFDerivAt P (coframeLinearMap η₁ η₂ x) x) ∧ Set.EqOn P id U := by
  obtain ⟨P, hPd, hPs⟩ := exists_smooth_development_of_closed_coframe
    (U := Set.univ) convex_univ isOpen_univ
    (fun x _ => h1r x) (fun x _ => h1θ x) (fun x _ => h2r x) (fun x _ => h2θ x)
    (fun x _ => hc1 x) (fun x _ => hc2 x)
  have hPs' : ∀ x, ContDiffAt ℝ ∞ P x := fun x => hPs x (mem_univ x)
  have hdid : ∀ x ∈ U, fderiv ℝ P x = ContinuousLinearMap.id ℝ PolarPoint := by
    intro x hx
    rw [(hPd x (mem_univ x)).fderiv]
    exact coframeLinearMap_eq_id_of_standard (hstd x hx).1 (hstd x hx).2.1
      (hstd x hx).2.2.1 (hstd x hx).2.2.2
  obtain ⟨Q, hQs, hQd, hQout⟩ :=
    exists_normalized_map_of_fderiv_eq_id_on_exterior hPs' hUo hUc hdid
  refine ⟨Q, hQs, ?_, hQout⟩
  intro x
  have hdQ : fderiv ℝ Q x = coframeLinearMap η₁ η₂ x :=
    (hQd x).trans (hPd x (mem_univ x)).fderiv
  rw [← hdQ]
  exact ((hQs x).differentiableAt (by simp)).hasFDerivAt

/-- A closed coframe which is nondegenerate everywhere and standard near infinity develops
to a globally invertible smooth map, with its actual coframe derivative. -/
theorem exists_global_development_of_closed_cartesian_coframe
    {η₁ η₂ : PlaneOneForm} {U K : Set PolarPoint}
    (h1r : ∀ x, ContDiffAt ℝ ∞ η₁.radial x)
    (h1θ : ∀ x, ContDiffAt ℝ ∞ η₁.angular x)
    (h2r : ∀ x, ContDiffAt ℝ ∞ η₂.radial x)
    (h2θ : ∀ x, ContDiffAt ℝ ∞ η₂.angular x)
    (hc1 : ∀ x, exteriorCoefficient η₁ x = 0)
    (hc2 : ∀ x, exteriorCoefficient η₂ x = 0)
    (hwedge : ∀ x, wedgeCoefficient η₁ η₂ x ≠ 0)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hstd : ∀ x ∈ U, η₁.radial x = 1 ∧ η₁.angular x = 0 ∧
      η₂.radial x = 0 ∧ η₂.angular x = 1)
    (hK : IsCompact K) (hout : Kᶜ ⊆ U) :
    ∃ e : PolarPoint ≃ₜ PolarPoint,
      (∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x) ∧
      (∀ y, ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y) ∧
      Set.EqOn e id U ∧
        ∀ x, HasFDerivAt (e : PolarPoint → PolarPoint) (coframeLinearMap η₁ η₂ x) x := by
  obtain ⟨P, hPs, hPd, hPout⟩ := exists_normalized_development_of_closed_cartesian_coframe
    h1r h1θ h2r h2θ hc1 hc2 hUo hUc hstd
  have hfix : ∀ x, x ∉ K → P x = x := fun x hx => hPout (hout hx)
  have hbij : ∀ x, Function.Bijective (fderiv ℝ P x) :=
    fun x => fderiv_bijective_of_hasFDerivAt_coframe (hPd x) (hwedge x)
  obtain ⟨e, he, hes, heis⟩ :=
    exists_smooth_homeomorph_of_eq_id_outside_compact hK hfix hPs hbij
  refine ⟨e, hes, heis, ?_, ?_⟩
  · simpa only [he] using hPout
  · intro x
    simpa only [he] using hPd x

/-- Full Cartesian reconstruction: integrate the actual flat connection, normalize its
primitive, rotate the actual Cartan coframe, and integrate the resulting closed forms.
The resulting development and its global inverse are both smooth. -/
theorem exists_global_development_of_flat_cartesian_coframe
    (d : FlatCartesianCoframe) {U K : Set PolarPoint}
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hzero : ∀ x ∈ U, d.connection.radial x = 0 ∧ d.connection.angular x = 0)
    (hstd : ∀ x ∈ U, d.first.radial x = 1 ∧ d.first.angular x = 0 ∧
      d.second.radial x = 0 ∧ d.second.angular x = 1)
    (hK : IsCompact K) (hout : Kᶜ ⊆ U) :
    ∃ (ψ : PolarPoint → ℝ) (e : PolarPoint ≃ₜ PolarPoint),
      (∀ x, HasFDerivAt ψ (d.connection.toCLM x) x) ∧
      (∀ x, ContDiffAt ℝ ∞ ψ x) ∧ Set.EqOn ψ 0 U ∧
      (∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x) ∧
      (∀ y, ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y) ∧
      Set.EqOn e id U ∧
      (∀ x, HasFDerivAt (e : PolarPoint → PolarPoint)
        (coframeLinearMap (rotatedCoframeOne ψ d.first d.second)
          (rotatedCoframeTwo ψ d.first d.second) x) x) ∧
      ∀ x v : PolarPoint,
        (fderiv ℝ (e : PolarPoint → PolarPoint) x v).1 ^ 2 +
          (fderiv ℝ (e : PolarPoint → PolarPoint) x v).2 ^ 2 =
            formValue d.first x v ^ 2 + formValue d.second x v ^ 2 := by
  obtain ⟨ψ, hψ, hψs, hψout⟩ := exists_global_smooth_primitive_zero_on_exterior
    (fun x => (d.connection_smooth x).1) (fun x => (d.connection_smooth x).2)
    d.connection_closed hUo hUc hzero
  have hdψ : coordinateDifferential ψ = d.connection := by
    apply PlaneOneForm.ext_components
    · funext x
      change radialPartial ψ x = d.connection.radial x
      unfold radialPartial
      rw [(hψ x).fderiv]
      simp [PlaneOneForm.toCLM_apply, formValue]
    · funext x
      change angularPartial ψ x = d.connection.angular x
      unfold angularPartial
      rw [(hψ x).fderiv]
      simp [PlaneOneForm.toCLM_apply, formValue]
  let ξ₁ := rotatedCoframeOne ψ d.first d.second
  let ξ₂ := rotatedCoframeTwo ψ d.first d.second
  have hξ : ∀ x, ContDiffAt ℝ ∞ ξ₁.radial x ∧ ContDiffAt ℝ ∞ ξ₁.angular x ∧
      ContDiffAt ℝ ∞ ξ₂.radial x ∧ ContDiffAt ℝ ∞ ξ₂.angular x := by
    intro x
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := d.coframe_smooth x
    exact ⟨contDiffAt_rotatedCoframeOne_radial (hψs x) h1r h2r,
      contDiffAt_rotatedCoframeOne_angular (hψs x) h1θ h2θ,
      contDiffAt_rotatedCoframeTwo_radial (hψs x) h1r h2r,
      contDiffAt_rotatedCoframeTwo_angular (hψs x) h1θ h2θ⟩
  have hclosed : ∀ x, exteriorCoefficient ξ₁ x = 0 ∧ exteriorCoefficient ξ₂ x = 0 := by
    intro x
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := d.coframe_smooth x
    have hc1 : exteriorCoefficient d.first x =
        wedgeCoefficient (coordinateDifferential ψ) d.second x := by
      rw [hdψ]
      exact d.cartan_first x
    have hc2 : exteriorCoefficient d.second x =
        -wedgeCoefficient (coordinateDifferential ψ) d.first x := by
      rw [hdψ]
      exact d.cartan_second x
    exact ⟨rotatedCoframeOne_closed (hψ x).differentiableAt
        (h1r.differentiableAt (by simp)) (h1θ.differentiableAt (by simp))
        (h2r.differentiableAt (by simp)) (h2θ.differentiableAt (by simp)) hc1 hc2,
      rotatedCoframeTwo_closed (hψ x).differentiableAt
        (h1r.differentiableAt (by simp)) (h1θ.differentiableAt (by simp))
        (h2r.differentiableAt (by simp)) (h2θ.differentiableAt (by simp)) hc1 hc2⟩
  have hwedge : ∀ x, wedgeCoefficient ξ₁ ξ₂ x ≠ 0 := by
    intro x
    exact rotatedCoframe_wedge_ne_zero (d.wedge_ne_zero x)
  have hξstd : ∀ x ∈ U, ξ₁.radial x = 1 ∧ ξ₁.angular x = 0 ∧
      ξ₂.radial x = 0 ∧ ξ₂.angular x = 1 := by
    intro x hx
    have hpx : ψ x = 0 := hψout hx
    simpa [ξ₁, ξ₂, rotatedCoframeOne, rotatedCoframeTwo, hpx] using hstd x hx
  obtain ⟨e, hes, heis, heout, hed⟩ :=
    exists_global_development_of_closed_cartesian_coframe
      (fun x => (hξ x).1) (fun x => (hξ x).2.1)
      (fun x => (hξ x).2.2.1) (fun x => (hξ x).2.2.2)
      (fun x => (hclosed x).1) (fun x => (hclosed x).2)
      hwedge hUo hUc hξstd hK hout
  refine ⟨ψ, e, hψ, hψs, hψout, hes, heis, heout, hed, ?_⟩
  intro x v
  rw [development_derivative_square_sum (η₁ := ξ₁) (η₂ := ξ₂) (hed x) v]
  exact rotatedCoframe_square_sum ψ d.first d.second x v

end ContinuousFlexibility
