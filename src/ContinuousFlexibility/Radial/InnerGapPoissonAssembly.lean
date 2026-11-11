import ContinuousFlexibility.Radial.InnerGapAssemblyData
import ContinuousFlexibility.Radial.InnerGapWeights
import ContinuousFlexibility.Radial.InnerDisjointPieces

/-!
# The actual finite gap Poisson sum and its reference normalization

All local Poisson columns live in the same physical radial L² space.
Their disjoint supports make their squared norms add exactly. The full
positive gap flux matrices therefore control the sum without a factor
depending on the number of gaps. Normalization uses the same full
reference matrix, including all off-diagonal gap entries.

A physical weight which is constant on each entire gap cancels the
reciprocal cut weight exactly. The weighted estimate consequently holds
for either sign, for the very same Poisson sum and reference matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InnerPositiveGapFamily

variable {D : ReferenceData} {γ ι : Type*} {j s : ℝ}
  (F : InnerPositiveGapFamily D γ j s)

theorem poisson_support (hw : Continuous D.w) (c : γ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (F.left c) (F.right c) →
      F.poisson hw c ξ r = 0 :=
  innerGapPoissonL2_support D hw (F.left_pos c) (F.in_core c)
    (fun r hr => (F.weight_pos c r (Ioo_subset_Icc_self hr)).le)
    (F.columns c) (F.columns_smooth c) ξ

theorem poisson_norm_sq_le (hw : ContDiff ℝ ∞ D.w) (hj : 0 < j) (hs : 0 < s)
    (c : γ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖F.poisson hw.continuous c ξ‖ ^ 2 ≤
      (Real.sqrt (12 / s) / j) ^ 2 * ⟪ξ, F.flux c ξ⟫_ℝ := by
  have hnorm := innerGapPoissonL2_norm_le D hw (F.ordered c) (F.left_pos c) hj hs
    (F.in_core c) (fun r hr => (F.weight_pos c r (Ioo_subset_Icc_self hr)).le)
    (F.columns c) (F.columns_smooth c) (F.columns_boundary c)
    (F.columns_homogeneous c) (F.weight_pos c) (F.slope_lower c) ξ
  have hnonneg := (F.flux_isPositive hw hs.le c).inner_nonneg_right ξ
  have hK : 0 ≤ Real.sqrt (12 / s) / j :=
    div_nonneg (Real.sqrt_nonneg _) hj.le
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK
    (Real.sqrt_nonneg ⟪ξ, F.flux c ξ⟫_ℝ))).mpr hnorm
  simpa only [poisson, mul_pow, Real.sq_sqrt hnonneg] using hsq

variable [Fintype γ] [Fintype ι]

/-- The actual gap columns are added after zero extension into one
physical Hilbert space. -/
def poissonSum (hw : Continuous D.w)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ ι →L[ℝ] RadialModeL2 D :=
  ∑ c, F.poisson hw c ∘L R c

theorem poissonSum_apply (hw : Continuous D.w)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ ι) :
    F.poissonSum hw R x = ∑ c, F.poisson hw c (R c x) := by
  simp only [poissonSum, sum_apply, ContinuousLinearMap.comp_apply]

/-- Actual physical disjointness, not an assumed operator orthogonality,
gives the exact squared-norm decomposition. -/
theorem poissonSum_norm_sq (hw : Continuous D.w)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ ι) :
    ‖F.poissonSum hw R x‖ ^ 2 = ∑ c, ‖F.poisson hw c (R c x)‖ ^ 2 := by
  rw [F.poissonSum_apply]
  exact innerL2_disjoint_sum_norm_sq
    (fun c => Ioo (F.left c) (F.right c)) F.disjoint
    (fun c => F.poisson hw c (R c x)) (fun c => F.poisson_support hw c (R c x))

theorem poissonSum_norm_sq_le (hw : ContDiff ℝ ∞ D.w) (hj : 0 < j) (hs : 0 < s)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ ι) :
    ‖F.poissonSum hw.continuous R x‖ ^ 2 ≤
      (Real.sqrt (12 / s) / j) ^ 2 * ∑ c, ⟪R c x, F.flux c (R c x)⟫_ℝ := by
  rw [F.poissonSum_norm_sq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun c _ => F.poisson_norm_sq_le hw hj hs c (R c x))

variable [DecidableEq ι]

/-- The actual full reference matrix controls the normalized physical
gap Poisson sum at scale j⁻¹. The constant is independent of gap length
and of the number of gaps. -/
theorem norm_poissonSum_normalized_le (hw : ContDiff ℝ ∞ D.w)
    (hj : 0 < j) (hs : 0 < s) (κ : ι → ℝ) (hκ : ∀ i, 0 < κ i)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    ‖F.poissonSum hw.continuous R ∘L
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt (F.referenceMatrix κ R))‖ ≤
      Real.sqrt (12 / s) / j := by
  let J := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
    (innerInterfaceInverseSqrt (F.referenceMatrix κ R))
  have hK : 0 ≤ Real.sqrt (12 / s) / j :=
    div_nonneg (Real.sqrt_nonneg _) hj.le
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  have henergy :
      ⟪J x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
        (F.referenceMatrix κ R) (J x)⟫_ℝ = ‖x‖ ^ 2 :=
    innerMatrix_inverseSqrt_energy (F.referenceMatrix κ R)
      (F.referenceMatrix_posDef hw hs.le κ hκ R) x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  calc
    ‖F.poissonSum hw.continuous R (J x)‖ ^ 2 ≤
        (Real.sqrt (12 / s) / j) ^ 2 * ∑ c, ⟪R c (J x), F.flux c (R c (J x))⟫_ℝ :=
      F.poissonSum_norm_sq_le hw hj hs R (J x)
    _ ≤ (Real.sqrt (12 / s) / j) ^ 2 *
        ⟪J x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
          (F.referenceMatrix κ R) (J x)⟫_ℝ :=
      mul_le_mul_of_nonneg_left
        (F.gap_energy_le_reference κ (fun i => (hκ i).le) R (J x)) (sq_nonneg _)
    _ = ((Real.sqrt (12 / s) / j) * ‖x‖) ^ 2 := by rw [henergy, mul_pow]

/-- Both endpoints of a gap have the same physical weight. Compatibility
of the actual boundary restriction with that scalar is sufficient for
exact cancellation, with no bound on the ratios between different gaps. -/
theorem poissonSum_multiplier_cancel (hw : Continuous D.w)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (W : ℝ → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ r, |W r| ≤ C)
    (c : γ → ℝ) (hc : ∀ g, c g ≠ 0)
    (hconstant : ∀ g, EqOn W (fun _ => c g) (Ioo (F.left g) (F.right g)))
    (Ω : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hRΩ : ∀ g x, R g (Ω x) = (c g)⁻¹ • R g x) :
    innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC ∘L
        F.poissonSum hw R ∘L Ω = F.poissonSum hw R := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, F.poissonSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [hRΩ g x]
  exact innerGapPoissonL2_multiplier_cancel D hw (F.left_pos g) (F.in_core g)
    (fun r hr => (F.weight_pos g r (Ioo_subset_Icc_self hr)).le)
    (F.columns g) (F.columns_smooth g) W hW C hWC (c g) (hc g) (hconstant g) (R g x)

/-- This theorem can be applied with either sign of the physical and
boundary weights. Both applications retain the identical actual
Poisson sum and canonical inverse square root of the full reference. -/
theorem norm_poissonSum_weighted_normalized_le (hw : ContDiff ℝ ∞ D.w)
    (hj : 0 < j) (hs : 0 < s) (κ : ι → ℝ) (hκ : ∀ i, 0 < κ i)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (W : ℝ → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ r, |W r| ≤ C)
    (c : γ → ℝ) (hc : ∀ g, c g ≠ 0)
    (hconstant : ∀ g, EqOn W (fun _ => c g) (Ioo (F.left g) (F.right g)))
    (Ω : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hRΩ : ∀ g x, R g (Ω x) = (c g)⁻¹ • R g x) :
    ‖(innerWeightMultiplier (radialHilbertMeasure D) W hW C hWC ∘L
        F.poissonSum hw.continuous R ∘L Ω) ∘L
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt (F.referenceMatrix κ R))‖ ≤
      Real.sqrt (12 / s) / j := by
  rw [F.poissonSum_multiplier_cancel hw.continuous R W hW C hWC c hc hconstant Ω hRΩ]
  exact F.norm_poissonSum_normalized_le hw hj hs κ hκ R

end InnerPositiveGapFamily

end ContinuousFlexibility.Radial
