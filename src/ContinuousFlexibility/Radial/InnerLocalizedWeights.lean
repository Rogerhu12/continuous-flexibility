module

public import ContinuousFlexibility.Radial.InnerWeightL2
public import ContinuousFlexibility.Radial.InnerDisjointPieces

/-!
# Local weight bounds in the physical L² space

All estimates below use the values of the actual multiplier on the support
of a local field. The absolute size of a common cell weight cancels between
the input and output estimates. Thus a global condition number is never
introduced into the inner Dirichlet or Poisson bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (W : α → ℝ) (hW : Measurable W) (C : ℝ)
  (hWC : ∀ x, |W x| ≤ C)

/-- Multiplication preserves the actual almost-everywhere support. -/
theorem innerWeightMultiplier_supported (s : Set α) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ∀ᵐ x ∂μ, x ∉ s → innerWeightMultiplier μ W hW C hWC f x = 0 := by
  filter_upwards [innerWeightMultiplier_ae μ W hW C hWC f, hf] with x hx hs
  intro hxs
  rw [hx, hs hxs, mul_zero]

/-- Only the weight on the support enters the norm bound. -/
theorem innerWeightMultiplier_norm_le_on_support (s : Set α) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) {K : ℝ}
    (hlocal : ∀ x ∈ s, |W x| ≤ K) :
    ‖innerWeightMultiplier μ W hW C hWC f‖ ≤ K * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [innerWeightMultiplier_ae μ W hW C hWC f, hf] with x hx hs
  rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  by_cases hxs : x ∈ s
  · exact mul_le_mul_of_nonneg_right (hlocal x hxs) (abs_nonneg _)
  · rw [hs hxs, abs_zero, mul_zero, mul_zero]

/-- A leading buffer sees exactly its cut weight, not an upper bound for
the weight on the rest of the cell. -/
theorem innerWeightMultiplier_eq_smul_of_support (s : Set α) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) (w : ℝ)
    (hconstant : ∀ x ∈ s, W x = w) :
    innerWeightMultiplier μ W hW C hWC f = w • f := by
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ W hW C hWC f,
    Lp.coeFn_smul w f, hf] with x hx hsmul hs
  rw [hx, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hxs : x ∈ s
  · rw [hconstant x hxs]
  · rw [hs hxs, mul_zero, mul_zero]

theorem innerWeightMultiplier_norm_eq_on_constant_support
    (s : Set α) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) (w : ℝ)
    (hconstant : ∀ x ∈ s, W x = w) :
    ‖innerWeightMultiplier μ W hW C hWC f‖ = |w| * ‖f‖ := by
  rw [innerWeightMultiplier_eq_smul_of_support μ W hW C hWC s f hf w hconstant,
    norm_smul, Real.norm_eq_abs]

/-- Weighting a finite orthogonal assembly preserves disjointness and
therefore still sums squared norms, with no cell-count factor. -/
theorem innerWeightMultiplier_disjoint_sum_norm_sq {ι : Type*} [Fintype ι]
    (s : ι → Set α) (hdis : Pairwise (fun i k => Disjoint (s i) (s k)))
    (f : ι → Lp ℝ 2 μ)
    (hf : ∀ i, ∀ᵐ x ∂μ, x ∉ s i → f i x = 0) :
    ‖innerWeightMultiplier μ W hW C hWC (∑ i, f i)‖ ^ 2 =
      ∑ i, ‖innerWeightMultiplier μ W hW C hWC (f i)‖ ^ 2 := by
  rw [map_sum]
  exact innerL2_disjoint_sum_norm_sq s hdis _
    (fun i => innerWeightMultiplier_supported μ W hW C hWC (s i) (f i) (hf i))

/-- A localized leading field and a remainder use their own supports. -/
theorem innerWeightMultiplier_local_decomposition_bound
    (s b : Set α) (p L R : Lp ℝ 2 μ) (hdecomp : p = L - R)
    (hL : ∀ᵐ x ∂μ, x ∉ b → L x = 0)
    (hR : ∀ᵐ x ∂μ, x ∉ s → R x = 0)
    (w : ℝ) (hconstant : ∀ x ∈ b, W x = w) {K : ℝ}
    (hlocal : ∀ x ∈ s, |W x| ≤ K) :
    ‖innerWeightMultiplier μ W hW C hWC p‖ ≤ |w| * ‖L‖ + K * ‖R‖ := by
  rw [hdecomp, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add
    (innerWeightMultiplier_norm_eq_on_constant_support μ W hW C hWC b L hL w hconstant).le
    (innerWeightMultiplier_norm_le_on_support μ W hW C hWC s R hR hlocal))

/-- Local reciprocal bounds cancel the common weight of a cell. The
operator and the input are the actual supported L² objects. -/
theorem innerWeightMultiplier_local_operator_bound
    (V : α → ℝ) (hV : Measurable V) (D : ℝ) (hVD : ∀ x, |V x| ≤ D)
    (s : Set α) (G : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hG : ∀ f, ∀ᵐ x ∂μ, x ∉ s → G f x = 0)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0)
    {R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w)
    (hlocalW : ∀ x ∈ s, |W x| ≤ R * w)
    (hlocalV : ∀ x ∈ s, |V x| ≤ R / w) :
    ‖innerWeightMultiplier μ W hW C hWC
      (G (innerWeightMultiplier μ V hV D hVD f))‖ ≤ R ^ 2 * ‖G‖ * ‖f‖ := by
  have hinput := innerWeightMultiplier_norm_le_on_support μ V hV D hVD s f hf hlocalV
  calc
    _ ≤ (R * w) * ‖G (innerWeightMultiplier μ V hV D hVD f)‖ :=
      innerWeightMultiplier_norm_le_on_support μ W hW C hWC s _ (hG _) hlocalW
    _ ≤ (R * w) * (‖G‖ * ‖innerWeightMultiplier μ V hV D hVD f‖) :=
      mul_le_mul_of_nonneg_left (G.le_opNorm _) (mul_nonneg hR hw.le)
    _ ≤ (R * w) * (‖G‖ * ((R / w) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinput (norm_nonneg G))
        (mul_nonneg hR hw.le)
    _ = R ^ 2 * ‖G‖ * ‖f‖ := by field_simp [hw.ne'] <;> ring

end ContinuousFlexibility.Radial
