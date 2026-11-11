import ContinuousFlexibility.Radial.InnerL2Restriction
import ContinuousFlexibility.Radial.InnerLocalizedWeights

/-!
# Actual orthogonal projections onto the inner pieces

Every projection is restriction followed by its genuine zero extension
in the same physical L² measure. Disjoint open pieces give a Bessel bound
with constant one, derived here from those projections. Multiplication by
either actual weight commutes with each piece projection.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)

def innerL2PieceProjection : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  innerL2ZeroExtension μ s ∘L LpToLpRestrictCLM α ℝ ℝ μ 2 s

theorem innerL2PieceProjection_ae (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    (innerL2PieceProjection μ s f : α → ℝ) =ᵐ[μ] s.indicator f :=
  innerL2ZeroExtension_restriction_ae μ s hs f

theorem innerL2PieceProjection_supported (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, x ∉ s → innerL2PieceProjection μ s f x = 0 := by
  filter_upwards [innerL2PieceProjection_ae μ s hs f] with x hx hxs
  rw [hx, indicator_of_notMem hxs]

theorem innerL2PieceProjection_eq_self (hs : MeasurableSet s) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : innerL2PieceProjection μ s f = f := by
  apply Lp.ext
  filter_upwards [innerL2PieceProjection_ae μ s hs f, hf] with x hx hz
  rw [hx]
  by_cases hxs : x ∈ s
  · exact indicator_of_mem hxs _
  · rw [indicator_of_notMem hxs, hz hxs]

theorem innerL2PieceProjection_norm_apply_le (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    ‖innerL2PieceProjection μ s f‖ ≤ ‖f‖ := by
  rw [innerL2PieceProjection, ContinuousLinearMap.comp_apply,
    innerL2ZeroExtension_norm μ s hs]
  exact innerL2Restriction_norm_apply_le μ s f

theorem norm_innerL2PieceProjection_le_one (hs : MeasurableSet s) :
    ‖innerL2PieceProjection μ s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using innerL2PieceProjection_norm_apply_le μ s hs f

theorem innerL2PieceProjection_selfAdjoint :
    IsSelfAdjoint (innerL2PieceProjection μ s) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  simp only [innerL2PieceProjection, ContinuousLinearMap.adjoint_comp,
    innerL2ZeroExtension_adjoint, innerL2ZeroExtension]

theorem innerL2PieceProjection_inner_self (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    ⟪innerL2PieceProjection μ s f, f⟫_ℝ = ‖innerL2PieceProjection μ s f‖ ^ 2 := by
  change ⟪(LpToLpRestrictCLM α ℝ ℝ μ 2 s).adjoint
      (LpToLpRestrictCLM α ℝ ℝ μ 2 s f), f⟫_ℝ =
    ‖innerL2ZeroExtension μ s (LpToLpRestrictCLM α ℝ ℝ μ 2 s f)‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    innerL2ZeroExtension_norm μ s hs]

/-- This identity applies to a weight and to its reciprocal without
differentiating either one. -/
theorem innerL2PieceProjection_weight_commute (hs : MeasurableSet s)
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C)
    (f : Lp ℝ 2 μ) :
    innerL2PieceProjection μ s (innerWeightMultiplier μ W hW C hWC f) =
      innerWeightMultiplier μ W hW C hWC (innerL2PieceProjection μ s f) := by
  apply Lp.ext
  filter_upwards [innerL2PieceProjection_ae μ s hs (innerWeightMultiplier μ W hW C hWC f),
    innerWeightMultiplier_ae μ W hW C hWC f,
    innerWeightMultiplier_ae μ W hW C hWC (innerL2PieceProjection μ s f),
    innerL2PieceProjection_ae μ s hs f] with x hP hWf hWP hPf
  rw [hP, hWP, hPf]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx, hWf]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

section FinitePieces

variable {ι : Type*} [Fintype ι] (sets : ι → Set α)
  (hmeas : ∀ i, MeasurableSet (sets i))
  (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))

/-- The support geometry yields the sum-of-squares identity for the
actual restrictions extended by zero. -/
theorem innerL2PieceProjections_sum_norm_sq (f : Lp ℝ 2 μ) :
    ‖∑ i, innerL2PieceProjection μ (sets i) f‖ ^ 2 =
      ∑ i, ‖innerL2PieceProjection μ (sets i) f‖ ^ 2 :=
  innerL2_disjoint_sum_norm_sq sets hdis _
    (fun i => innerL2PieceProjection_supported μ (sets i) (hmeas i) f)

/-- No coverage assumption is needed for Bessel's inequality, so it also
applies to a subcollection of model pieces or of positive gaps. -/
theorem innerL2PieceProjections_bessel (f : Lp ℝ 2 μ) :
    (∑ i, ‖innerL2PieceProjection μ (sets i) f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  let g := ∑ i, innerL2PieceProjection μ (sets i) f
  have hsum : ‖g‖ ^ 2 = ∑ i, ‖innerL2PieceProjection μ (sets i) f‖ ^ 2 :=
    innerL2PieceProjections_sum_norm_sq μ sets hmeas hdis f
  have hinner : ⟪g, f⟫_ℝ = ‖g‖ ^ 2 := by
    dsimp only [g]
    rw [sum_inner, innerL2PieceProjections_sum_norm_sq μ sets hmeas hdis f]
    exact Finset.sum_congr rfl (fun i _ => innerL2PieceProjection_inner_self μ
      (sets i) (hmeas i) f)
  have hle : ‖g‖ ^ 2 ≤ ‖g‖ * ‖f‖ := by
    rw [← hinner]
    exact real_inner_le_norm g f
  have hnorm : ‖g‖ ≤ ‖f‖ := by
    by_cases hg : ‖g‖ = 0
    · rw [hg]
      exact norm_nonneg f
    · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
      apply le_of_not_gt
      intro hgt
      have hlt := mul_lt_mul_of_pos_left hgt hgpos
      exact (not_lt_of_ge (show ‖g‖ * ‖g‖ ≤ ‖g‖ * ‖f‖ by
        simpa only [pow_two] using hle)) hlt
  rw [← hsum]
  exact (sq_le_sq₀ (norm_nonneg g) (norm_nonneg f)).mpr hnorm

/-- If the source is supported in the union of the pieces, their actual
zero extensions recover that very source. -/
theorem innerL2PieceProjections_sum_eq (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ ⋃ i, sets i → f x = 0) :
    (∑ i, innerL2PieceProjection μ (sets i) f) = f := by
  classical
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => innerL2PieceProjection μ (sets i) f),
    ae_all_iff.mpr (fun i => innerL2PieceProjection_ae μ (sets i) (hmeas i) f), hf]
      with x hsum hproj hz
  rw [hsum]
  by_cases hx : ∃ i, x ∈ sets i
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · rw [hproj i, indicator_of_mem hi]
    · intro k _ hki
      have hk : x ∉ sets k := fun h => (Set.disjoint_left.mp (hdis hki)) h hi
      rw [hproj k, indicator_of_notMem hk]
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim
  · have hzero : f x = 0 := hz (by simpa only [mem_iUnion] using hx)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    rw [hproj i, indicator_of_notMem (fun h => hx ⟨i, h⟩)]

end FinitePieces

end ContinuousFlexibility.Radial
