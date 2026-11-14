import ContinuousFlexibility.Analysis.WholeReferenceGaugePositiveGeometryJets

/-!
# The same positive inverse and source factor as scalar-source data

The inverse is the literal inverse of the already selected coordinate.
Its range follows from the actual positive component, while its positive
jets are recovered from the normalized inverse-radial atom. The source
factor is the displayed scalar of the same coordinate and height. Only
numerical constants vary with the derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

theorem fixedPositiveReference_scalarSource_material_data
    {D : ReferenceData} (hprofile : Continuous (deriv D.w))
    (W : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hW : ∀ i, 1 ≤ W i) {B : ℝ} (hB : 1 ≤ B)
    (hwidth : ∀ i, n04PositiveRight i - n04PositiveLeft i ≤ B * W i ^ B ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B * W i ^ B)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ A * W i ^ A ∧
        |iteratedDeriv k (H i) x| ≤ A * W i ^ A ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ A * W i ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤ A * W i ^ A) :
    (∀ i, ContDiff ℝ ∞ (Function.invFun (Y i)) ∧
      ContDiff ℝ ∞ (positiveReferenceGeometryScalar
        (n04PositiveLeft i) (n04PositiveRight i) (Y i) (H i) .sourceFactor) ∧
      ∀ x, x ∈ Ioo (0 : ℝ) 1 → Function.invFun (Y i) x ∈ radialCore D) ∧
    ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i x,
      x ∈ Ioo (0 : ℝ) 1 → ∀ k, k ≤ N →
        |iteratedDeriv k (positiveReferenceGeometryScalar
          (n04PositiveLeft i) (n04PositiveRight i) (Y i) (H i) .sourceFactor) x| ≤
            A * W i ^ A ∧
        (1 ≤ k → |iteratedDeriv k (Function.invFun (Y i)) x| ≤ A * W i ^ A) := by
  have hlr (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hprofile i).2.1
  refine ⟨?_, ?_⟩
  · intro i
    have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
      contDiff_id.prodMk contDiff_const
    have hχ : ContDiff ℝ ∞ (Function.invFun (Y i)) := by
      simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
        (hgeometry i).inverse_smooth.fst.comp hline
    refine ⟨hχ, positiveReferenceGeometryScalar_smooth (hgeometry i) .sourceFactor, ?_⟩
    intro x hx
    have himage := (hgeometry i).inverse_maps_open (x := (x, 0)) ⟨hx, mem_univ _⟩
    exact n04PositiveComponent_interval_subset hprofile i himage.1
  · intro N
    obtain ⟨M, hM, hfinite⟩ := fixedPositiveReference_geometry_material_jets W hW
      n04PositiveLeft n04PositiveRight hlr hB hwidth Y H hgeometry hjets N
    let A : ℝ := max M (max (B * M) (B + M))
    have hMA : M ≤ A := le_max_left _ _
    have hBMA : B * M ≤ A := (le_max_left _ _).trans (le_max_right _ _)
    have hBplusMA : B + M ≤ A := (le_max_right _ _).trans (le_max_right _ _)
    have hA : 1 ≤ A := hM.trans hMA
    refine ⟨A, hA, ?_⟩
    intro i x hx k hk
    have hWi : 0 < W i := zero_lt_one.trans_le (hW i)
    have hMcost : M * W i ^ M ≤ A * W i ^ A :=
      mul_le_mul hMA (Real.rpow_le_rpow_of_exponent_le (hW i) hMA)
        (Real.rpow_nonneg hWi.le _) (zero_le_one.trans hA)
    refine ⟨(hfinite i .sourceFactor x hx k hk).trans hMcost, ?_⟩
    intro hkpos
    have hgap : 0 < n04PositiveRight i - n04PositiveLeft i := sub_pos.mpr (hlr i)
    have he : Function.invFun (Y i) = (fun t : ℝ => n04PositiveLeft i +
        (n04PositiveRight i - n04PositiveLeft i) *
          positiveReferenceGeometryScalar (n04PositiveLeft i) (n04PositiveRight i)
            (Y i) (H i) .inverseRadial t) := by
      funext t
      dsimp only [positiveReferenceGeometryScalar]
      field_simp [hgap.ne'] <;> ring
    calc
      |iteratedDeriv k (Function.invFun (Y i)) x| =
          (n04PositiveRight i - n04PositiveLeft i) *
            |iteratedDeriv k (positiveReferenceGeometryScalar
              (n04PositiveLeft i) (n04PositiveRight i) (Y i) (H i) .inverseRadial) x| := by
        rw [he, iteratedDeriv_const_add (by omega : 0 < k),
          iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hgap]
      _ ≤ (B * W i ^ B) * (M * W i ^ M) :=
        mul_le_mul (hwidth i).1 (hfinite i .inverseRadial x hx k hk)
          (abs_nonneg _) (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg hWi.le _))
      _ = (B * M) * W i ^ (B + M) := by
        rw [Real.rpow_add hWi]
        ring
      _ ≤ A * W i ^ A :=
        mul_le_mul hBMA (Real.rpow_le_rpow_of_exponent_le (hW i) hBplusMA)
          (Real.rpow_nonneg hWi.le _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
