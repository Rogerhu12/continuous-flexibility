module

public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Radial.R11bTensorL2

/-!
# The cubic perturbation estimate in the actual L² space

A measurable output dominated in square by finitely many L² fields belongs to L², with
the corresponding Hilbert norm bound. The cubic differential estimate supplies exactly
five such weighted derivative fields. The measure is arbitrary, so the same result applies
to canonical-piece measures and cylinder measures without changing the source model.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter ContinuousFlexibility.Radial
open scoped BigOperators

/-- Square domination by any finite family gives membership and the sharp integrated norm
estimate. The separate measurability hypothesis on the dominated function is essential. -/
theorem n06_memLp_of_square_le_finiteSum
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {f : α → ℝ} (g : ι → α → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hpoint : ∀ᵐ x ∂μ, f x ^ 2 ≤ K * ∑ i, g i x ^ 2) :
    ∃ h : MemLp f 2 μ,
      ‖h.toLp f‖ ^ 2 ≤ K * ∑ i, ‖(hg i).toLp (g i)‖ ^ 2 ∧
      ‖h.toLp f‖ ≤ Real.sqrt K * Real.sqrt (∑ i, ‖(hg i).toLp (g i)‖ ^ 2) := by
  have hsum : Integrable (fun x => ∑ i, g i x ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hg i).integrable_sq)
  have hmajor : Integrable (fun x => K * ∑ i, g i x ^ 2) μ := hsum.const_mul K
  have hsq : Integrable (fun x => f x ^ 2) μ := by
    apply hmajor.mono' (hf.pow 2)
    filter_upwards [hpoint] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))] using hx
  let h : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf).mpr hsq
  have hnorm : ‖h.toLp f‖ ^ 2 ≤ K * ∑ i, ‖(hg i).toLp (g i)‖ ^ 2 := by
    rw [r11b_norm_toLp_sq h]
    calc
      (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, K * ∑ i, g i x ^ 2 ∂μ :=
        integral_mono_ae hsq hmajor hpoint
      _ = K * ∑ i, ∫ x, g i x ^ 2 ∂μ := by
        rw [integral_const_mul,
          integral_finsetSum Finset.univ (fun i _ => (hg i).integrable_sq)]
      _ = K * ∑ i, ‖(hg i).toLp (g i)‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact (r11b_norm_toLp_sq (hg i)).symm
  refine ⟨h, hnorm, ?_⟩
  calc
    ‖h.toLp f‖ ≤ Real.sqrt (K * ∑ i, ‖(hg i).toLp (g i)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le hnorm
    _ = Real.sqrt K * Real.sqrt (∑ i, ‖(hg i).toLp (g i)‖ ^ 2) := by
      rw [Real.sqrt_mul hK]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff

/-- The five actual weighted derivatives of the positive-cylinder graph estimate. -/
def n06CubicGraphFields (d u : PolarPoint → ℝ) : Fin 5 → PolarPoint → ℝ :=
  ![fun p => d p ^ 2 * radialPartial (radialPartial u) p,
    fun p => d p ^ 2 * Real.sqrt (d p) * angularPartial (radialPartial u) p,
    fun p => d p ^ 3 * angularPartial (angularPartial u) p,
    fun p => d p * radialPartial u p,
    fun p => d p * Real.sqrt (d p) * angularPartial u p]

theorem n06CubicGraphFields_square_sum (d u : PolarPoint → ℝ) (p : PolarPoint)
    (hd : 0 ≤ d p) :
    (∑ i, (n06CubicGraphFields d u i p) ^ 2) =
      d p ^ 4 * (radialPartial (radialPartial u) p) ^ 2 +
      d p ^ 5 * (angularPartial (radialPartial u) p) ^ 2 +
      d p ^ 6 * (angularPartial (angularPartial u) p) ^ 2 +
      d p ^ 2 * (radialPartial u p) ^ 2 + d p ^ 3 * (angularPartial u p) ^ 2 := by
  simp [n06CubicGraphFields, Fin.sum_univ_succ, mul_pow, Real.sq_sqrt hd] <;> ring

/-- The actual operator difference belongs to the original L² space when the five graph
fields do. The pointwise input is exactly `n06_divergenceDifference_sq_le`, used a.e. -/
theorem n06_divergenceDifference_memLp_of_graph_bound
    {μ : Measure PolarPoint} {L L₀ : SymmetricCoefficients}
    {d u : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hmeas : AEStronglyMeasurable
      (fun p => divergenceOperator L u p - divergenceOperator L₀ u p) μ)
    (hgraph : ∀ i, MemLp (n06CubicGraphFields d u i) 2 μ)
    (hd : ∀ᵐ p ∂μ, 0 ≤ d p)
    (hpoint : ∀ᵐ p ∂μ,
      (divergenceOperator L u p - divergenceOperator L₀ u p) ^ 2 ≤
        125 * δ ^ 2 *
          (d p ^ 4 * (radialPartial (radialPartial u) p) ^ 2 +
           d p ^ 5 * (angularPartial (radialPartial u) p) ^ 2 +
           d p ^ 6 * (angularPartial (angularPartial u) p) ^ 2 +
           d p ^ 2 * (radialPartial u p) ^ 2 + d p ^ 3 * (angularPartial u p) ^ 2)) :
    ∃ h : MemLp (fun p => divergenceOperator L u p - divergenceOperator L₀ u p) 2 μ,
      ‖h.toLp (fun p => divergenceOperator L u p - divergenceOperator L₀ u p)‖ ^ 2 ≤
        125 * δ ^ 2 * ∑ i, ‖(hgraph i).toLp (n06CubicGraphFields d u i)‖ ^ 2 ∧
      ‖h.toLp (fun p => divergenceOperator L u p - divergenceOperator L₀ u p)‖ ≤
        Real.sqrt 125 * δ *
          Real.sqrt (∑ i, ‖(hgraph i).toLp (n06CubicGraphFields d u i)‖ ^ 2) := by
  have hsum : ∀ᵐ p ∂μ,
      (divergenceOperator L u p - divergenceOperator L₀ u p) ^ 2 ≤
        (125 * δ ^ 2) * ∑ i, (n06CubicGraphFields d u i p) ^ 2 := by
    filter_upwards [hd, hpoint] with p hdp hp
    rw [n06CubicGraphFields_square_sum d u p hdp]
    exact hp
  obtain ⟨h, hsquare, hnorm⟩ := n06_memLp_of_square_le_finiteSum
    (n06CubicGraphFields d u) (K := 125 * δ ^ 2) (by positivity) hmeas hgraph hsum
  refine ⟨h, hsquare, ?_⟩
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 125), Real.sqrt_sq hδ] using hnorm

/-- Smooth core inputs supply the measurability hypothesis without any representative choices. -/
theorem n06_divergenceDifference_aestronglyMeasurable
    {μ : Measure PolarPoint} {L L₀ : SymmetricCoefficients} {u : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (ha₀ : ContDiff ℝ ∞ L₀.a) (hb₀ : ContDiff ℝ ∞ L₀.b)
    (hc₀ : ContDiff ℝ ∞ L₀.c) (hu : ContDiff ℝ ∞ u) :
    AEStronglyMeasurable
      (fun p => divergenceOperator L u p - divergenceOperator L₀ u p) μ :=
  ((contDiff_divergenceOperator ha hb hc hu).continuous.sub
    (contDiff_divergenceOperator ha₀ hb₀ hc₀ hu).continuous).aestronglyMeasurable

end ContinuousFlexibility.Statements
