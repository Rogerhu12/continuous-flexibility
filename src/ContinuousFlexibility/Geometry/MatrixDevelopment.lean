module

public import ContinuousFlexibility.Geometry.CartesianMetricCoframe
public import ContinuousFlexibility.Geometry.CartesianExterior

/-!
# Development of an actual flat Cartesian matrix metric

This binds the Cholesky construction to the whole-plane Poincare and global
inversion theorems. The flatness hypothesis is the vanishing actual exterior
derivative of the explicitly constructed matrix connection, not the existence
of any development.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

def flatCartesianCoframeOfMatrix (A B C : PolarPoint → ℝ)
    (hs : ∀ x, ContDiffAt ℝ ∞ A x ∧ ContDiffAt ℝ ∞ B x ∧ ContDiffAt ℝ ∞ C x)
    (hA : ∀ x, 0 < A x) (hD : ∀ x, 0 < matrixDiscriminant A B C x)
    (hflat : ∀ x, exteriorCoefficient (matrixCoframeConnection A B C) x = 0) :
    FlatCartesianCoframe where
  connection := matrixCoframeConnection A B C
  first := matrixCoframeOne A B C
  second := matrixCoframeTwo A B C
  connection_smooth := fun x => contDiffAt_matrixCoframeConnection
    (hs x).1 (hs x).2.1 (hs x).2.2 (hA x) (hD x)
  coframe_smooth := fun x => contDiffAt_matrixCoframe
    (hs x).1 (hs x).2.1 (hs x).2.2 (hA x) (hD x)
  connection_closed := hflat
  cartan_first := fun x => (matrixCoframe_cartan (hA x) (hD x)).1
  cartan_second := fun x => (matrixCoframe_cartan (hA x) (hD x)).2
  wedge_ne_zero := fun x => (matrixCoframe_wedge_pos (hA x) (hD x)).ne'

/-- A smooth positive definite Cartesian matrix, Euclidean outside a disk and with
zero actual connection curvature, has an exterior-normalized smooth global development. -/
theorem exists_global_development_of_flat_matrix_on_disk
    (A B C : PolarPoint → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, ContDiffAt ℝ ∞ A x ∧ ContDiffAt ℝ ∞ B x ∧ ContDiffAt ℝ ∞ C x)
    (hA : ∀ x, 0 < A x) (hD : ∀ x, 0 < matrixDiscriminant A B C x)
    (hflat : ∀ x, exteriorCoefficient (matrixCoframeConnection A B C) x = 0)
    (hstd : ∀ x : PolarPoint, R < ‖Complex.equivRealProdCLM.symm x‖ →
      A x = 1 ∧ B x = 0 ∧ C x = 1) :
    ∃ e : PolarPoint ≃ₜ PolarPoint,
      (∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x) ∧
      (∀ y, ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y) ∧
      (∀ x, R < ‖Complex.equivRealProdCLM.symm x‖ → e x = x) ∧
      e '' {x | ‖Complex.equivRealProdCLM.symm x‖ ≤ R} =
        {x | ‖Complex.equivRealProdCLM.symm x‖ ≤ R} ∧
      ∀ x v : PolarPoint,
        (fderiv ℝ (e : PolarPoint → PolarPoint) x v).1 ^ 2 +
          (fderiv ℝ (e : PolarPoint → PolarPoint) x v).2 ^ 2 =
            A x * v.1 ^ 2 + 2 * B x * v.1 * v.2 + C x * v.2 ^ 2 := by
  let d := flatCartesianCoframeOfMatrix A B C hs hA hD hflat
  have hz : ∀ x : PolarPoint, R < ‖Complex.equivRealProdCLM.symm x‖ →
      d.connection.radial x = 0 ∧ d.connection.angular x = 0 := by
    intro x hx
    have hU := (isOpen_complex_radius_exterior R).mem_nhds hx
    have h1 : A =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [hU] with y hy
      exact (hstd y hy).1
    have h2 : B =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hU] with y hy
      exact (hstd y hy).2.1
    have h3 : C =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [hU] with y hy
      exact (hstd y hy).2.2
    exact matrixCoframeConnection_zero_of_eventually_standard h1 h2 h3
  have hds : ∀ x : PolarPoint, R < ‖Complex.equivRealProdCLM.symm x‖ →
      d.first.radial x = 1 ∧ d.first.angular x = 0 ∧
      d.second.radial x = 0 ∧ d.second.angular x = 1 := by
    intro x hx
    exact matrixCoframe_standard (hstd x hx).1 (hstd x hx).2.1 (hstd x hx).2.2
  obtain ⟨e, hes, heis, heout, heimage, hemetric⟩ :=
    exists_global_development_of_flat_cartesian_coframe_on_disk d hR hz hds
  refine ⟨e, hes, heis, heout, heimage, ?_⟩
  intro x v
  exact (hemetric x v).trans (matrixCoframe_square_sum (hA x) (hD x).le v)

end ContinuousFlexibility
