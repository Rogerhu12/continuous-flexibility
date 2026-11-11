import ContinuousFlexibility.Radial.InnerAdmissibleSource
import ContinuousFlexibility.Radial.InnerBorderWeights
import ContinuousFlexibility.Radial.InnerIsometricRestriction

/-!
# Actual weights on the supported admissible source

Multiplication by a bounded measurable function preserves the genuine
physical support and fixes the unique scalar coordinate. Thus both the
weight and its reciprocal restrict to the same closed Hilbert source.
A coefficient-loss multiplier is the same construction with bound one.

The inclusion remains isometric. Ambient operator estimates and actual
Poisson adjoints therefore transfer without a norm-equivalence loss.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (s : Set α) (hs : MeasurableSet s) (bordered : Bool)

local notation "S" => innerSupportedAdmissibleSource μ s bordered
local notation "H" => ↥S

include μ s hs bordered

theorem innerSupportedAdmissibleSource_supported (F : H) :
    ∀ᵐ x ∂μ, x ∉ s → F.val.fst x = 0 := by
  have hmem := (mem_innerSupportedAdmissibleSource μ s bordered F.val).mp F.property
  have h := innerL2PieceProjection_supported μ s hs F.val.fst
  rwa [hmem.2] at h

/-- Actual multiplication preserves support and the scalar-zero kernel. -/
theorem innerSupportedWeightMultiplier_mem (W : α → ℝ) (hW : Measurable W)
    (C : ℝ) (hWC : ∀ x, |W x| ≤ C) (F : H) :
    innerBorderFieldMap μ (innerWeightMultiplier μ W hW C hWC) F.val ∈ S := by
  have hmem := (mem_innerSupportedAdmissibleSource μ s bordered F.val).mp F.property
  apply (mem_innerSupportedAdmissibleSource μ s bordered _).mpr
  rw [innerBorderFieldMap_fst, innerBorderFieldMap_snd]
  refine ⟨hmem.1, ?_⟩
  apply innerL2PieceProjection_eq_self μ s hs
  exact innerWeightMultiplier_supported μ W hW C hWC s F.val.fst
    (innerSupportedAdmissibleSource_supported μ s hs bordered F)

/-- The genuine field multiplier on the same supported source. Its
scalar coordinate is the identity, including in the bordered case. -/
def innerSupportedWeightMultiplier (W : α → ℝ) (hW : Measurable W)
    (C : ℝ) (hWC : ∀ x, |W x| ≤ C) : H →L[ℝ] H :=
  ((innerBorderFieldMap μ (innerWeightMultiplier μ W hW C hWC)).comp
    (S).toSubmodule.subtypeL).codRestrict (S).toSubmodule (fun F => by
      apply (ClosedSubmodule.mem_toSubmodule_iff _ S).mpr
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        innerSupportedWeightMultiplier_mem μ s hs bordered W hW C hWC F)

@[simp] theorem innerSupportedWeightMultiplier_apply
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) (F : H) :
    (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC F).val =
      innerBorderFieldMap μ (innerWeightMultiplier μ W hW C hWC) F.val := by
  unfold innerSupportedWeightMultiplier
  exact (ContinuousLinearMap.coe_codRestrict_apply _ _ _ F).trans
    (by rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply])

theorem innerSupportedWeightMultiplier_field_ae
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) (F : H) :
    ((innerSupportedWeightMultiplier μ s hs bordered W hW C hWC F).val.fst : α → ℝ)
      =ᵐ[μ] fun x => W x * F.val.fst x := by
  rw [innerSupportedWeightMultiplier_apply, innerBorderFieldMap_fst]
  exact innerWeightMultiplier_ae μ W hW C hWC F.val.fst

@[simp] theorem innerSupportedWeightMultiplier_scalar
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) (F : H) :
    (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC F).val.snd = F.val.snd := by
  rw [innerSupportedWeightMultiplier_apply, innerBorderFieldMap_snd]

theorem norm_innerSupportedWeightMultiplier_le_ambient
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) :
    ‖innerSupportedWeightMultiplier μ s hs bordered W hW C hWC‖ ≤
      ‖innerBorderFieldMap μ (innerWeightMultiplier μ W hW C hWC)‖ := by
  apply innerIsometricOperator_norm_le (S).toSubmodule.subtypeₗᵢ (S).toSubmodule.subtypeₗᵢ
  intro F
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] using
    innerSupportedWeightMultiplier_apply μ s hs bordered W hW C hWC F

theorem norm_innerSupportedWeightMultiplier_le
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hC : 1 ≤ C)
    (hWC : ∀ x, |W x| ≤ C) :
    ‖innerSupportedWeightMultiplier μ s hs bordered W hW C hWC‖ ≤ C :=
  (norm_innerSupportedWeightMultiplier_le_ambient μ s hs bordered W hW C hWC).trans
    (norm_innerBorderFieldMap_le μ _ hC
      (norm_innerWeightMultiplier_le μ W hW C (zero_le_one.trans hC) hWC))

/-- In particular the actual coefficient-loss multiplier is a
contraction, while the single scalar is retained unchanged. -/
theorem norm_innerSupportedCoefficientLoss_le_one
    (loss : α → ℝ) (hloss : Measurable loss) (hbound : ∀ x, |loss x| ≤ 1) :
    ‖innerSupportedWeightMultiplier μ s hs bordered loss hloss 1 hbound‖ ≤ 1 :=
  norm_innerSupportedWeightMultiplier_le μ s hs bordered loss hloss 1 le_rfl hbound

theorem innerSupportedWeightMultiplier_selfAdjoint
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) :
    IsSelfAdjoint (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC) := by
  apply innerIsometricRestriction_selfAdjoint (H := H) (E := InnerBorderL2 μ)
    (S).toSubmodule.subtypeₗᵢ
    (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC)
    (innerBorderFieldMap μ (innerWeightMultiplier μ W hW C hWC))
  · intro F
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] using
      innerSupportedWeightMultiplier_apply μ s hs bordered W hW C hWC F
  · exact innerBorderFieldMap_selfAdjoint μ _
      (innerWeightMultiplier_selfAdjoint μ W hW C hWC)

section Equivalence

variable (W : α → ℝ) (hW : Measurable W) (hpos : ∀ x, 0 < W x)
  (C Cinv : ℝ) (hWC : ∀ x, |W x| ≤ C) (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv)

/-- The actual weight and its actual reciprocal on the same supported
physical Hilbert space. -/
def innerSupportedWeightEquiv : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.equivOfInverse
    (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC)
    (innerSupportedWeightMultiplier μ s hs bordered (fun x => (W x)⁻¹) hW.inv Cinv hWinv)
    (by
      intro F
      apply Subtype.ext
      simp only [innerSupportedWeightMultiplier_apply, innerBorderFieldMap_apply,
        WithLp.toLp_fst, WithLp.toLp_snd]
      rw [innerWeightMultiplier_comp_apply μ W (fun x => (W x)⁻¹)
        hW hW.inv C Cinv hWC hWinv (fun x => inv_mul_cancel₀ (hpos x).ne')]
      exact WithLp.toLp_ofLp 2 F.val)
    (by
      intro F
      apply Subtype.ext
      simp only [innerSupportedWeightMultiplier_apply, innerBorderFieldMap_apply,
        WithLp.toLp_fst, WithLp.toLp_snd]
      rw [innerWeightMultiplier_comp_apply μ (fun x => (W x)⁻¹) W
        hW.inv hW Cinv C hWinv hWC (fun x => mul_inv_cancel₀ (hpos x).ne')]
      exact WithLp.toLp_ofLp 2 F.val)

theorem innerSupportedWeightEquiv_apply (F : H) :
    (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv F).val =
      innerBorderWeightEquiv μ (innerWeightEquiv μ W hW hpos C Cinv hWC hWinv) F.val := by
  rw [innerSupportedWeightEquiv, ContinuousLinearEquiv.equivOfInverse_apply,
    innerSupportedWeightMultiplier_apply, innerBorderFieldMap_apply,
    innerBorderWeightEquiv_apply, innerWeightEquiv_apply]

theorem innerSupportedWeightEquiv_symm_apply (F : H) :
    ((innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv).symm F).val =
      (innerBorderWeightEquiv μ (innerWeightEquiv μ W hW hpos C Cinv hWC hWinv)).symm F.val := by
  rw [innerSupportedWeightEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply, innerSupportedWeightMultiplier_apply,
    innerBorderFieldMap_apply, innerBorderWeightEquiv_symm_apply, innerWeightEquiv_symm_apply]

theorem innerSupportedWeightEquiv_toCLM :
    (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv : H →L[ℝ] H) =
      innerSupportedWeightMultiplier μ s hs bordered W hW C hWC := by
  unfold innerSupportedWeightEquiv
  exact ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse _ _ _ _

theorem innerSupportedWeightEquiv_symm_toCLM :
    ((innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv).symm :
      H →L[ℝ] H) =
      innerSupportedWeightMultiplier μ s hs bordered (fun x => (W x)⁻¹) hW.inv Cinv hWinv := by
  unfold innerSupportedWeightEquiv
  rw [ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse]

theorem innerSupportedWeightEquiv_selfAdjoint :
    IsSelfAdjoint
      (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv : H →L[ℝ] H) := by
  rw [innerSupportedWeightEquiv_toCLM]
  exact innerSupportedWeightMultiplier_selfAdjoint μ s hs bordered W hW C hWC

end Equivalence

end ContinuousFlexibility.Radial
