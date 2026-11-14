module

public import ContinuousFlexibility.Analysis.PositiveReferenceGeometryJetEnvelope

/-!
# Geometric material jets for one fixed positive reference family

The low interval cost and every forward/inverse jet belong to the same
coordinate and height. A finite prefix changes numerical constants only;
the original sample weight, family and interpolation width are retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff BigOperators

theorem fixedPositiveReference_geometry_material_jets
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (l r : ι → ℝ) (hlr : ∀ i, l i < r i)
    {B : ℝ} (hB : 1 ≤ B)
    (hwidth : ∀ i, r i - l i ≤ B * W i ^ B ∧ (r i - l i)⁻¹ ≤ B * W i ^ B)
    (Y H : ι → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (l i) (r i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ A * W i ^ A ∧
        |iteratedDeriv k (H i) x| ≤ A * W i ^ A ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ A * W i ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤ A * W i ^ A) :
    ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i (v : Atom) (x : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → ∀ k, k ≤ N →
        |iteratedDeriv k (positiveReferenceGeometryScalar (l i) (r i) (Y i) (H i) v) x| ≤
          M * W i ^ M := by
  classical
  choose A hA hactual using hjets
  intro N
  obtain ⟨C, hC, hfinite⟩ := exists_positiveReferenceGeometry_jet_envelope N
  let D : ℝ := 1 + B + ∑ j : Fin (N + 1), A j.val
  have hsum : 0 ≤ ∑ j : Fin (N + 1), A j.val :=
    Finset.sum_nonneg (fun j _ => zero_le_one.trans (hA j.val))
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hB, hsum]
  have hBD : B ≤ D := by dsimp only [D]; linarith only [hsum]
  have hAD (j : ℕ) (hj : j ≤ N) : A j ≤ D := by
    have hjSum := Finset.single_le_sum
      (f := fun j : Fin (N + 1) => A j.val)
      (fun j _ => zero_le_one.trans (hA j.val))
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (N + 1)))
    dsimp only [D]
    linarith only [hjSum, hB]
  let coefficient : ℝ := C * D ^ (2 * N + 2)
  let exponent : ℝ := D * ((2 * N + 2 : ℕ) : ℝ)
  let M : ℝ := 1 + coefficient + exponent
  have hcoefficient : 0 < coefficient :=
    mul_pos (zero_lt_one.trans_le hC) (pow_pos (zero_lt_one.trans_le hD) _)
  have hexponent : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hD) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by
    dsimp only [M]; linarith only [hexponent]
  have hexponentM : exponent ≤ M := by dsimp only [M]; linarith only [hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i v x hx k hk
  let Z : ℝ := D * W i ^ D
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow (hW i) (zero_le_one.trans hD))
  have hcost (a : ℝ) (ha : a ≤ D) : a * W i ^ a ≤ Z :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le (hW i) ha)
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (zero_le_one.trans hD)
  have hYj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N + 1) (t : ℝ) :
      |iteratedDeriv j (Y i) t| ≤ Z := by
    have hh := ((hactual N i).1 (j - 1) (by omega) t).1
    rw [Nat.sub_add_cancel hj] at hh
    exact hh.trans (hcost (A N) (hAD N le_rfl))
  have hHj (j : ℕ) (hj : j ≤ N) (t : ℝ) :
      |iteratedDeriv j (H i) t| ≤ Z ∧
      |iteratedDeriv j (fun u => (H i u)⁻¹) t| ≤ Z := by
    have hh := ((hactual N i).1 j hj t).2
    exact ⟨hh.1.trans (hcost (A N) (hAD N le_rfl)),
      hh.2.trans (hcost (A N) (hAD N le_rfl))⟩
  have hχj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N + 1) (t : ℝ) :
      |iteratedDeriv j (Function.invFun (Y i)) t| ≤ Z := by
    have hh := (hactual (j - 1) i).2 t
    rw [Nat.sub_add_cancel hj] at hh
    exact hh.trans (hcost (A (j - 1)) (hAD (j - 1) (by omega)))
  have hb := hfinite hZ (hlr i)
    ((hwidth i).1.trans (hcost B hBD)) ((hwidth i).2.trans (hcost B hBD))
    (Y i) (H i) (hgeometry i) hYj hHj hχj v x hx k hk
  apply hb.trans
  calc
    C * Z ^ (2 * N + 2) = coefficient * W i ^ exponent := by
      dsimp only [Z, coefficient, exponent]
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hW i)) D (2 * N + 2)]
      ring
    _ ≤ coefficient * W i ^ M := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW i) hexponentM) hcoefficient.le
    _ ≤ M * W i ^ M := mul_le_mul_of_nonneg_right hcoefficientM
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)

end ContinuousFlexibility.Analysis
