module

public import ContinuousFlexibility.Analysis.SpacesCompactHeights
public import ContinuousFlexibility.Analysis.SpacesHeightBounds
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.TameTransfer
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The physical compatibility functional and its projection

The physical source integral is the integral in the manuscript, with
ordinary radial density and normalized angular mean. Its continuity and
fixed tame loss follow from the order-two point-evaluation estimate.
The cutoff derivative supplies a compactly supported normalizer, so the
projection onto compatible sources is an actual continuous linear map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem spaces_continuous_angularMean {f : PolarPoint → ℝ} (hf : Continuous f) :
    Continuous (fun r => angularMean (fun θ => f (r, θ))) := by
  have h : Continuous (fun r : ℝ => ∫ θ in Icc (0 : ℝ) Real.pi, f (r, θ)) :=
    continuous_parametric_integral_of_continuous (f := fun r θ => f (r, θ)) hf isCompact_Icc
  have he : (fun r : ℝ => angularMean (fun θ => f (r, θ))) =
      fun r => (1 / Real.pi) * ∫ θ in Icc (0 : ℝ) Real.pi, f (r, θ) := by
    funext r
    rw [angularMean, intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Icc_eq_integral_Ioc]
  rw [he]
  exact continuous_const.mul h

theorem spaces_angularMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun θ => f θ + g θ) = angularMean f + angularMean g := by
  rw [angularMean, angularMean, angularMean,
    intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_add]

theorem spaces_angularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun θ => c * f θ) = c * angularMean f := by
  rw [angularMean, angularMean, intervalIntegral.integral_const_mul]
  ring

theorem spaces_physicalSourceIntegral_add (D : ReferenceData) {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    physicalSourceIntegral D (f + g) =
      physicalSourceIntegral D f + physicalSourceIntegral D g := by
  have he : (fun r => angularMean (fun θ => (f + g) (r, θ))) =
      fun r => angularMean (fun θ => f (r, θ)) + angularMean (fun θ => g (r, θ)) := by
    funext r
    exact spaces_angularMean_add
      (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id))
  rw [physicalSourceIntegral, he,
    intervalIntegral.integral_add
      ((spaces_continuous_angularMean hf).intervalIntegrable _ _)
      ((spaces_continuous_angularMean hg).intervalIntegrable _ _)]
  rfl

theorem spaces_physicalSourceIntegral_smul (D : ReferenceData) (c : ℝ)
    (f : PolarPoint → ℝ) :
    physicalSourceIntegral D (c • f) = c • physicalSourceIntegral D f := by
  simp only [physicalSourceIntegral, Pi.smul_apply, smul_eq_mul,
    spaces_angularMean_const_mul, intervalIntegral.integral_const_mul]

/-- The normalized angular integral has norm at most the uniform bound. -/
theorem spaces_angularMean_abs_le {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ θ, |f θ| ≤ C) : |angularMean f| ≤ C := by
  have hi' : ‖∫ θ in (0 : ℝ)..Real.pi, f θ‖ ≤ C * |Real.pi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (f := f)
      (fun θ _ => by simpa only [Real.norm_eq_abs] using h θ)
  have hi : |∫ θ in (0 : ℝ)..Real.pi, f θ| ≤ C * Real.pi := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos Real.pi_pos] using
      hi'
  rw [angularMean, abs_mul, abs_of_pos (div_pos zero_lt_one Real.pi_pos)]
  calc
    (1 / Real.pi) * |∫ θ in (0 : ℝ)..Real.pi, f θ| ≤
        (1 / Real.pi) * (C * Real.pi) :=
      mul_le_mul_of_nonneg_left hi (div_pos zero_lt_one Real.pi_pos).le
    _ = C := by field_simp

theorem spaces_physicalSourceIntegral_abs_le {D : ReferenceData} {f : PolarPoint → ℝ}
    {C : ℝ} (h : ∀ p, |f p| ≤ C) :
    |physicalSourceIntegral D f| ≤ C * |D.b - D.a| := by
  simpa only [physicalSourceIntegral, Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := D.a) (b := D.b)
      (f := fun r => angularMean (fun θ => f (r, θ)))
      (fun r _ => by
        rw [Real.norm_eq_abs]
        exact spaces_angularMean_abs_le (fun θ => h (r, θ))))

private theorem spaces_rankOne_properties {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Q : E →L[ℝ] ℝ) (ψ : E) (hψ : Q ψ = 1) :
    (∀ f, Q (Analysis.rankOneProjection Q ψ f) = 0) ∧
      (∀ f, Q f = 0 → Analysis.rankOneProjection Q ψ f = f) := by
  constructor
  · intro f
    rw [Analysis.rankOneProjection_apply, map_sub, map_smul, hψ, smul_eq_mul,
      mul_one, sub_self]
  · intro f hf
    rw [Analysis.rankOneProjection_apply, hf, zero_smul, sub_zero]

section SourceModel

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
  {H : SobolevModelData} (hH : IsSobolevModel D T (3 / 4 : ℝ) H)

include hT hH

private theorem spaces_source_decode_continuous (u : H.Space) : Continuous (H.decode u) :=
  (heightMember_contDiff_and_flatJets hT (by norm_num : (0 : ℝ) < 3 / 4)
    (hH.2.2.2.1 u)).1.continuous

/-- The real linear map given by the actual physical source integral. -/
def spacesSourceLinear : H.Space →ₗ[ℝ] ℝ where
  toFun u := physicalSourceIntegral D (H.decode u)
  map_add' := by
    intro u v
    rw [map_add]
    exact spaces_physicalSourceIntegral_add D
      (spaces_source_decode_continuous hT hH u) (spaces_source_decode_continuous hT hH v)
  map_smul' := by
    intro c u
    rw [map_smul]
    exact spaces_physicalSourceIntegral_smul D c (H.decode u)

@[simp] theorem spacesSourceLinear_apply (u : H.Space) :
    spacesSourceLinear hT hH u = physicalSourceIntegral D (H.decode u) := rfl

theorem spacesSourceLinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H.Space,
      |spacesSourceLinear hT hH u| ≤ C * H.grading 2 u := by
  obtain ⟨B, hB, hbound⟩ := spaces_height_uniform_bound hT (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨B * |D.b - D.a|, mul_nonneg hB (abs_nonneg _), fun u => ?_⟩
  have hu := hH.2.2.2.1 u
  have h := spaces_physicalSourceIntegral_abs_le (D := D) (fun p => hbound (H.decode u) hu p)
  have hn : physicalNorm T (3 / 4 : ℝ) 2 (H.decode u) = ‖u.val 2‖ :=
    (hH.2.2.2.2.2.2.2 u 2).symm
  rw [hn] at h
  calc
    |spacesSourceLinear hT hH u| ≤ B * ‖u.val 2‖ * |D.b - D.a| := h
    _ ≤ B * H.grading 2 u * |D.b - D.a| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Analysis.norm_coordinate_le_graded _ _ (le_refl 2) u) hB) (abs_nonneg _)
    _ = (B * |D.b - D.a|) * H.grading 2 u := by ring

theorem spacesSourceLinear_isTame :
    Analysis.IsTameLinear H.grading realGrading (spacesSourceLinear hT hH) 0 2 := by
  obtain ⟨C, hC, hbound⟩ := spacesSourceLinear_bound hT hH
  intro s hs
  refine ⟨⟨C, hC⟩, fun u => ?_⟩
  change ‖spacesSourceLinear hT hH u‖ ≤ C * H.grading (s + 0) u
  rw [Real.norm_eq_abs, Nat.add_zero]
  exact (hbound u).trans (mul_le_mul_of_nonneg_left
    (Analysis.gradedSeminorm_monotone _ _ hs u) hC)

/-- The compatibility functional, with its verified continuous topology. -/
def spacesSourceFunctional : H.Space →L[ℝ] ℝ where
  toLinearMap := spacesSourceLinear hT hH
  cont := by
    obtain ⟨C, hC, hbound⟩ := spacesSourceLinear_bound hT hH
    apply (Analysis.withSeminorms_graded _ _).continuous_real_rng
    refine ⟨{2}, ⟨C, hC⟩, fun u => ?_⟩
    simp only [Finset.sup_singleton, smul_apply, NNReal.smul_def, smul_eq_mul]
    exact (le_abs_self (spacesSourceLinear hT hH u)).trans (hbound u)

@[simp] theorem spacesSourceFunctional_apply (u : H.Space) :
    spacesSourceFunctional hT hH u = physicalSourceIntegral D (H.decode u) := rfl

theorem spaces_source_normalizer (hD : IsAccumulatingProfile D) :
    ∃ ψ : H.Space, HasCompactRadialSupport D (H.decode ψ) ∧
      spacesSourceFunctional hT hH ψ = 1 := by
  obtain ⟨χ, hχ⟩ := spaces_exists_cutoff_of_accumulating hD
  obtain ⟨f, hf, hc, hQ⟩ := spaces_exists_compact_normalizer hT hχ (3 / 4 : ℝ)
  obtain ⟨ψ, hψ⟩ := hH.2.2.2.2.1 f hf
  refine ⟨ψ, ?_, ?_⟩
  · rwa [hψ]
  · rw [spacesSourceFunctional_apply, hψ, hQ]

theorem spaces_source_projection (ψ : H.Space)
    (hψ : spacesSourceFunctional hT hH ψ = 1) :
    ∃ P : H.Space →L[ℝ] H.Space,
      (∀ f, P f = f - spacesSourceFunctional hT hH f • ψ) ∧
      (∀ f, spacesSourceFunctional hT hH (P f) = 0) ∧
      (∀ f, spacesSourceFunctional hT hH f = 0 → P f = f) ∧
      Analysis.IsTameLinear H.grading H.grading P.toLinearMap 0 2 := by
  let Q := spacesSourceFunctional hT hH
  let P := Analysis.rankOneProjection Q ψ
  obtain ⟨C, hC, hbound⟩ := spacesSourceLinear_bound hT hH
  have hprops := spaces_rankOne_properties Q ψ hψ
  refine ⟨P, fun f => Analysis.rankOneProjection_apply Q ψ f, hprops.1, hprops.2, ?_⟩
  exact Analysis.rankOneProjection_isTameLinear (p := H.grading) Q ψ
    (fun m n hmn u => Analysis.gradedSeminorm_monotone _ _ hmn u) hC hbound

end SourceModel

end ContinuousFlexibility.Statements
