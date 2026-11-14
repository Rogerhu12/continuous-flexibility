module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceCosts
public import ContinuousFlexibility.Analysis.N04RealizationFixedRadialEnvelope

/-!
# The fixed reference inverse has a controlled chain-coefficient mass

The fixed radial pullback uses the chain coefficients already present
in the exact derivative formula. Their finite sums have a common cost
before the positive component, point and output order in the prefix are
chosen. The bound concerns the same reference inverse retained by the
assembly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- Extract the genuine scalar smoothness from the displayed cylinder
geometry, without choosing a new scalar interpolation. -/
theorem n04PositiveGeometry_reference_scalar_geometry
    {Y H : ℝ → ℝ} {l r : ℝ}
    (h : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1) :
    ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
      ContDiff ℝ ∞ H ∧ (∀ x, 0 < H x) := by
  have hline : ContDiff ℝ ∞ (fun x : ℝ => (x, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  exact ⟨h.chart_smooth.fst.comp hline, h.inverse_smooth.fst.comp hline,
    h.height_smooth.comp hline, fun x => h.height_positive (x, 0)⟩

/-- Every coefficient mass through the requested spatial prefix has
the same enlarged-material envelope at the original component sample. -/
theorem n04PositiveGeometry_reference_chain_mass_material_cost
    {ι : Type*} {T : MaterialData} {cell : ι → ℕ} {Y H : ι → ℝ → ℝ}
    (hfloor : ∀ x, 1 ≤ T.E0 x)
    (h : N04PositiveReferenceMaterialBounds T cell Y H)
    (hχ : ∀ i, ContDiff ℝ ∞ (Function.invFun (Y i))) (s : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i, ∀ a : ℕ, a ≤ s → ∀ x : ℝ,
      (∑ j : Fin (a + 1), |radialChainCoefficient (Function.invFun (Y i)) a j x|) ≤
        B * (enlargedMaterialData T).E0 (T.sample (cell i)) ^ B := by
  let E : (ι × ℝ) → ℝ := fun z => (enlargedMaterialData T).E0 (T.sample (cell z.1))
  have hE (z : ι × ℝ) : 1 ≤ E z := (hfloor _).trans (le_enlargedMaterialData_E0 T _)
  have hjet (j : ℕ) (hj : 0 < j) : HasPositiveEnvelope E
      (fun z : ι × ℝ => ‖iteratedFDeriv ℝ j (Function.invFun (Y z.1)) z.2‖) := by
    obtain ⟨B, hB, hb⟩ := n04PositiveGeometry_reference_prefix_material_cost hfloor h (j - 1)
    refine ⟨B, B, zero_lt_one.trans_le hB, zero_lt_one.trans_le hB, ?_⟩
    intro z
    have he : j - 1 + 1 = j := by omega
    simpa only [E, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, he] using
      (hb z.1 (j - 1) le_rfl z.2).2.1
  let F : Fin (s + 1) → (ι × ℝ) → ℝ := fun a z =>
    ∑ j : Fin (a.val + 1), |radialChainCoefficient (Function.invFun (Y z.1)) a.val j z.2|
  have hF (a : Fin (s + 1)) : HasPositiveEnvelope E (F a) :=
    n04Realization_radialChainCoefficientMass_envelope hE Prod.snd
      (fun z : ι × ℝ => Function.invFun (Y z.1)) (fun z => hχ z.1) hjet a.val
  obtain ⟨C, A, hC, hA, hb⟩ := n04Realization_envelope_finite_uniform hE F
    (fun a z => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hF
  obtain ⟨B0, hB0, hpack⟩ := coefficientEnvelope_pack C A
  let B := max 1 B0
  have hB : 1 ≤ B := le_max_left _ _
  have hBB : B0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro i a ha x
  have hbound := hb (i, x) (⟨a, Nat.lt_succ_of_le ha⟩ : Fin (s + 1))
  exact hbound.trans ((hpack (E (i, x)) (hE (i, x))).trans
    (mul_le_mul hBB (Real.rpow_le_rpow_of_exponent_le (hE (i, x)) hBB)
      (Real.rpow_nonneg (zero_le_one.trans (hE (i, x))) _) (zero_le_one.trans hB)))

end ContinuousFlexibility.Analysis
