module

public import ContinuousFlexibility.Contracts.CartesianFlatness
public import ContinuousFlexibility.Geometry.MatrixDevelopment

/-!
# Actual global planar development of the analytic core

This theorem constructs the development from the height equation and the
global smooth extensions in `FlatAnnularCore`. A planar development, a
primitive, or Cartesian flatness is not an additional input. Existence of
the analytic core itself remains the nonlinear existence obligation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

theorem coordinate_pair_eq_matrix_of_square_sum
    (L : PolarPoint →L[ℝ] PolarPoint) (a b c : ℝ)
    (hmetric : ∀ v : PolarPoint,
      (L v).1 ^ 2 + (L v).2 ^ 2 = a * v.1 ^ 2 + 2 * b * v.1 * v.2 + c * v.2 ^ 2)
    (u v : PolarPoint) :
    coordinateEuclideanPair (L u) (L v) =
      a * u.1 * v.1 + b * (u.1 * v.2 + u.2 * v.1) + c * u.2 * v.2 := by
  have hu := hmetric u
  have hv := hmetric v
  have huv := hmetric (u + v)
  simp only [map_add, Prod.fst_add, Prod.snd_add] at huv
  unfold coordinateEuclideanPair
  nlinarith

/-- The same actual height and profile produce a genuine globally
invertible, exterior-normalized Euclidean development of `g-dz²`. -/
theorem FlatAnnularCore.exists_planarDevelopment (A : FlatAnnularCore) :
    ∃ e : PolarPoint ≃ₜ PolarPoint,
      ContDiff ℝ ∞ (e : PolarPoint → PolarPoint) ∧
      ContDiff ℝ ∞ (e.symm : PolarPoint → PolarPoint) ∧
      (∀ x, A.b < cartesianRadius x → e x = x) ∧
      e '' {x | cartesianRadius x ≤ A.b} = {x | cartesianRadius x ≤ A.b} ∧
      ∀ x u v : PolarPoint,
        coordinateEuclideanPair (fderiv ℝ (e : PolarPoint → PolarPoint) x u)
          (fderiv ℝ (e : PolarPoint → PolarPoint) x v) =
            cartesianRemainder A.w A.cartesianHeight x u v := by
  obtain ⟨hA, hB, hC⟩ := A.contDiff_cartesianRemainder_entries
  obtain ⟨e, he, hei, hout, himage, hmetric⟩ :=
    exists_global_development_of_flat_matrix_on_disk
      (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight)
      (cartesianRemainderC A.w A.cartesianHeight) A.b_pos.le
      (fun _ => ⟨hA.contDiffAt, hB.contDiffAt, hC.contDiffAt⟩)
      A.cartesianRemainderA_pos A.cartesianRemainder_det_pos
      A.cartesianRemainderConnection_closed
      (fun _ hx => A.cartesianRemainder_standard_right hx)
  refine ⟨e, contDiff_iff_contDiffAt.mpr he, contDiff_iff_contDiffAt.mpr hei,
    hout, himage, ?_⟩
  intro x u v
  calc
    _ = cartesianRemainderA A.w A.cartesianHeight x * u.1 * v.1 +
        cartesianRemainderB A.w A.cartesianHeight x * (u.1 * v.2 + u.2 * v.1) +
          cartesianRemainderC A.w A.cartesianHeight x * u.2 * v.2 :=
      coordinate_pair_eq_matrix_of_square_sum _ _ _ _ (hmetric x) u v
    _ = _ := (cartesianRemainder_matrix A.w A.cartesianHeight x u v).symm

theorem image_larger_disk_of_normalized_homeomorph
    (e : PolarPoint ≃ₜ PolarPoint) {b R : ℝ} (hbR : b ≤ R)
    (hout : ∀ x, b < cartesianRadius x → e x = x) :
    e '' {x | cartesianRadius x ≤ R} = {x | cartesianRadius x ≤ R} := by
  apply image_eq_self_of_bijective_eq_id_outside e.bijective
  intro x hx
  apply hout x
  exact hbR.trans_lt (lt_of_not_ge hx)

end ContinuousFlexibility
