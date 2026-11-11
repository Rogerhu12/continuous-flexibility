import ContinuousFlexibility.Analysis.N01cReferenceJetBounds
import ContinuousFlexibility.Analysis.N01cMaterialNormalization

/-!
# Transport of the retained primitive reference geometry

The radial construction records an optical lower bound in its discrete
reference envelope. The already proved reference/material comparison
converts it to the exact sampled envelope used by N01. This conversion
uses the same profile, cells, material data and chosen controls throughout.
No coefficient, speed or flow estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- An upper comparison of positive envelopes gives a lower comparison
of their negative powers, with one constant in both positions. -/
theorem exists_negativePower_comparison_constant
    {K C A : ℝ} (hK : 0 < K) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∀ R E : ℝ, 0 < R → 1 ≤ E →
      R ^ K ≤ C * E ^ A → B⁻¹ * E ^ (-B) ≤ K⁻¹ * R ^ (-K) := by
  let B : ℝ := max 1 (max A (K * C))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hAB : A ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : K * C ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, fun R E hR hE hcompare => ?_⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hbound : K * R ^ K ≤ B * E ^ B := by
    calc
      K * R ^ K ≤ K * (C * E ^ A) := mul_le_mul_of_nonneg_left hcompare hK.le
      _ = (K * C) * E ^ A := (mul_assoc _ _ _).symm
      _ ≤ B * E ^ B := mul_le_mul hKC
        (Real.rpow_le_rpow_of_exponent_le hE hAB)
        (Real.rpow_nonneg hEpos.le A) hB.le
  have hinv := one_div_le_one_div_of_le
    (mul_pos hK (Real.rpow_pos_of_pos hR K)) hbound
  simpa only [one_div, mul_inv_rev, Real.rpow_neg, mul_comm] using hinv

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- The original control geometry consists of actual negative components. -/
theorem n01_negativeRadialComponent
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (m : ℕ) :
    NegativeRadialComponent D (C.left m) (C.right m) :=
  ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
    (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩

/-- The strengthened radial construction supplies the nonlinear primitive
geometry once the chosen component is attached to its actual cell.
The envelope normalization is a proved replacement of material data. -/
theorem n01PrimitiveGeometry_of_radialConstruction
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hR : RadialConstructionGeometry D)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) :
    N01PrimitiveGeometry D T S C := by
  obtain ⟨hχ, K, hK, hlower⟩ := hR
  obtain ⟨C₀, A, hC₀, _, hcompare⟩ :=
    radialE_cell_rpow_le_E0 hT hA.1.1 hE K hK.le
  obtain ⟨B, hB, hnegative⟩ := exists_negativePower_comparison_constant
    (A := A) hK hC₀
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  have hpart : RadialPartition D := hA.1.1.choose_spec.2.1
  refine ⟨hloc, hχ, B, hB, fun m r hr => ?_⟩
  have hEone : 1 ≤ T.E0 (T.sample (C.cell m)) :=
    hE _ (hpart.2.2.2.1 _ (hsample _))
  have hweight := hnegative (radialE (D.cellIndex (C.cell m)))
    (T.E0 (T.sample (C.cell m))) (Real.exp_pos _) hEone
      (hcompare _ _ (hsample _))
  have hδ : 0 ≤ min (r - C.left m) (C.right m - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  exact (mul_le_mul_of_nonneg_right hweight hδ).trans
    (hlower (C.left m) (C.right m) (C.cell m)
      (n01_negativeRadialComponent hA.2.2.1 m) (hloc m) r hr)

end ContinuousFlexibility.Blueprint
