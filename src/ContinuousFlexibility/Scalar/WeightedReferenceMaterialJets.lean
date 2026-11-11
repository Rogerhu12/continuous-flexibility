import ContinuousFlexibility.Scalar.WeightedMaterialRadiusJets

/-!
# Actual reference coefficients in material coordinates

These instances concern the given profile and radius, including the
reciprocal profile. Ordinary reference inverse jets are first bounded by
arbitrarily small powers of the envelope, then transported by the actual
radius. Smooth coefficients on a neighborhood of the closed physical
interval are handled by compactness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData}

private theorem scalar_reference_contDiffOn_iteratedDeriv {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

/-- A coefficient smooth on a neighborhood of the closed annulus has
subpower material jets. -/
theorem materialSubpower_comp_radius_of_contDiffOn (hT : IsMaterialData D T)
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hclosed : Icc D.a D.b ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    MaterialSubpower T (fun x => f (T.radius x)) := by
  have hopen : Ioo D.a D.b ⊆ U :=
    fun r hr => hclosed ⟨hr.1.le, hr.2.le⟩
  apply materialSubpower_comp_radius hT (hf.mono hopen)
  intro n ε hε
  have hn := scalar_reference_contDiffOn_iteratedDeriv hU hf n
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image
    (hn.continuousOn.abs.mono hclosed)
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hb : |iteratedDeriv n f r| ≤ max B 0 :=
    (hB ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩).trans (le_max_left _ _)
  have hM : 1 ≤ T.M r ^ ε :=
    Real.one_le_rpow (hT.2.1 r hr).2.2.2 hε.le
  exact hb.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM (le_max_right B 0))

theorem materialSubpower_comp_radius_of_contDiff (hT : IsMaterialData D T)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    MaterialSubpower T (fun x => f (T.radius x)) :=
  materialSubpower_comp_radius_of_contDiffOn hT isOpen_univ (subset_univ _) hf.contDiffOn

private theorem scalar_reference_radialJet_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ) :
    radialJet n f = iteratedDeriv n f := by
  induction n with
  | zero => exact iteratedDeriv_zero.symm
  | succ n ih => rw [radialJet, ih, iteratedDeriv_succ]

/-- The actual reciprocal reference profile, with all material jets, grows
more slowly than every positive power of the fixed envelope. -/
theorem referenceInverse_material_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    MaterialSubpower T (fun x => (D.w (T.radius x))⁻¹) := by
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hwpos : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hB.1.2.2.2.2.1
  apply materialSubpower_comp_radius hT
    (hw.contDiffOn.inv (fun r hr => (hwpos r hr).ne'))
  intro n ε hε
  obtain ⟨K, hK, hb⟩ := referenceInverseJet_le_subpowerM ⟨B, hB⟩ hT n hε
  refine ⟨K, hK.le, fun r hr => ?_⟩
  simpa only [scalar_reference_radialJet_eq_iteratedDeriv] using hb r hr

theorem referenceProfile_material_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    MaterialSubpower T (fun x => D.w (T.radius x)) := by
  obtain ⟨B, hB⟩ := hD
  exact materialSubpower_comp_radius_of_contDiff hT hB.1.2.2.1.1

theorem referenceProfile_deriv_material_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    MaterialSubpower T (fun x => deriv D.w (T.radius x)) := by
  obtain ⟨B, hB⟩ := hD
  exact materialSubpower_comp_radius_of_contDiff hT
    (contDiff_infty_iff_deriv.mp hB.1.2.2.1.1).2

theorem materialRadius_subpower (hT : IsMaterialData D T) :
    MaterialSubpower T T.radius :=
  materialSubpower_of_bounded_jets hT hT.2.2.2.2.2.2.1
    (iteratedDeriv_materialRadius_bounded hT)

theorem materialRadius_inv_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    MaterialSubpower T (fun x => (T.radius x)⁻¹) := by
  obtain ⟨B, hB⟩ := hD
  have ha : 0 < D.a := hB.1.1
  apply materialSubpower_comp_radius_of_contDiffOn hT isOpen_Ioi
    (fun r hr => show 0 < r from ha.trans_le hr.1)
  exact (contDiffOn_id : ContDiffOn ℝ ∞ (fun r : ℝ => r) (Ioi (0 : ℝ))).inv
    (fun r hr => (show 0 < r from hr).ne')

end ContinuousFlexibility.Statements
