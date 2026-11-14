module

public import ContinuousFlexibility.Radial.TailLowSynthesisForm
public import ContinuousFlexibility.Radial.TailCoreAverages

/-!
# The actual low-mode projection

Weighted mass averages and the normalized smooth hats define a bounded
projection on each admissible Friedrichs form space. On the compact smooth
core the averages have finite support, so this projection preserves the
core. Its complementary part has zero average on every active mass cell.
The two quantitative energy estimates therefore apply to all form vectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff lp
open ContinuousFlexibility.Statements

/-- On a smooth core vector the actual coefficient analysis is finitely
supported, regardless of whether the wall is finite or the endpoint. -/
theorem tailLowAnalysis_finite_on_core (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (hcut : cut ≤ T.endpoint) (u : tailGradientSpace T cut)
    (hu : u ∈ tailGradientCore T cut) :
    ∃ a : TailLowIndex T cut →₀ ℝ,
      tailLowAnalysis T hT cut (tailFormBase T cut u) = tailFiniteEmbedding a := by
  classical
  obtain ⟨N, hN⟩ := tailGradientCore_mass_averages_eventually_zero hT hcut hu
  let b : ℓ²(TailLowIndex T cut, ℝ) := tailLowAnalysis T hT cut (tailFormBase T cut u)
  let s : Finset (TailLowIndex T cut) :=
    (Finset.range N).subtype (fun n => tailFirstMassIndex T ≤ n ∧ T.node (n + 1) ≤ cut)
  have hs : ∀ i : TailLowIndex T cut, b i ≠ 0 → i ∈ s := by
    intro i hi
    apply Finset.mem_subtype.mpr
    apply Finset.mem_range.mpr
    by_contra hn
    apply hi
    dsimp only [b]
    rw [tailLowAnalysis_apply, hN i (le_of_not_gt hn), mul_zero]
  let a : TailLowIndex T cut →₀ ℝ := Finsupp.onFinset s b hs
  refine ⟨a, ?_⟩
  apply lp.ext
  funext i
  rw [tailFiniteEmbedding_apply, Finsupp.onFinset_apply]

/-- The projection is built from the actual mass cells and actual smooth
resistance hats, with no abstract inverse among its inputs. -/
def tailActualLowProjection (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) : tailGradientSpace T cut →L[ℝ] tailGradientSpace T cut :=
  tailLowProjection (tailFormBase T cut) (tailLowAnalysis T hT cut)
    (tailNormalizedHat T hT cut)

theorem tailActualLowProjection_apply (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (u : tailGradientSpace T cut) :
    tailActualLowProjection T hT cut u = tailSynthesis (tailNormalizedHat T hT cut)
      (tailLowAnalysis T hT cut (tailFormBase T cut u)) :=
  tailLowProjection_apply _ _ _ _

theorem tailActualLowProjection_idempotent (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (u : tailGradientSpace T cut) :
    tailActualLowProjection T hT cut (tailActualLowProjection T hT cut u) =
      tailActualLowProjection T hT cut u := by
  exact tailLowProjection_idempotent (tailNormalizedHat_finite_bound T hT cut)
    (tailFormBase T cut) (tailLowAnalysis T hT cut)
    (tailNormalizedHat_analysis T hT cut) u

theorem tailNormalizedHat_linearCombination_core (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a ∈ tailGradientCore T cut := by
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a)]
  apply tailGradientCore_sum
  intro i _
  apply tailGradientCore_smul
  exact (mem_tailGradientCore_iff T cut _).mpr (tailNormalizedHat_core T hT cut i)

theorem tailActualLowProjection_preserves_core (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (hcut : cut ≤ T.endpoint)
    (u : tailGradientSpace T cut) (hu : u ∈ tailGradientCore T cut) :
    tailActualLowProjection T hT cut u ∈ tailGradientCore T cut := by
  obtain ⟨a, ha⟩ := tailLowAnalysis_finite_on_core T hT cut hcut u hu
  rw [tailActualLowProjection_apply, ha,
    tailSynthesis_on_finite (tailNormalizedHat_finite_bound T hT cut)]
  exact tailNormalizedHat_linearCombination_core T hT cut a

theorem tailActualLowProjection_high_analysis_zero (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (u : tailGradientSpace T cut) :
    tailLowAnalysis T hT cut
      (tailFormBase T cut (u - tailActualLowProjection T hT cut u)) = 0 :=
  tailLowProjection_high_analysis_zero (tailNormalizedHat_finite_bound T hT cut)
    (tailFormBase T cut) (tailLowAnalysis T hT cut)
    (tailNormalizedHat_analysis T hT cut) u

/-- The residual has zero mean on every active cell. Cells after a finite
wall are zero by the actual Friedrichs form boundary condition. -/
theorem tailActualLowProjection_high_means (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (hcut : TailAdmissibleCut T cut)
    (u : tailGradientSpace T cut) (n : ℕ) (hn : tailFirstMassIndex T ≤ n) :
    (∫ x in tailMassCell T n,
      (tailFormBase T cut (u - tailActualLowProjection T hT cut u)) x
        ∂deepTailMeasure T) = 0 := by
  rcases tailAdmissibleCut_cell_dichotomy hT hcut n with hbefore | hafter
  · let i : TailLowIndex T cut := ⟨n, hn, hbefore⟩
    have hz := congrArg (fun a : ℓ²(TailLowIndex T cut, ℝ) => a i)
      (tailActualLowProjection_high_analysis_zero T hT cut u)
    rw [tailLowAnalysis_apply] at hz
    simp only [lp.coeFn_zero, Pi.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (inv_ne_zero (Real.sqrt_pos.mpr (tailMass_pos hT n)).ne')
  · exact tailForm_mass_average_zero_after_cut _ n hafter

theorem tailActualLowProjection_low_energy (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (u : tailGradientSpace T cut) :
    ‖tailFormGradient T cut (tailActualLowProjection T hT cut u)‖ ^ 2 ≤
      (5 * tailSmoothStepConstant * T.Λ / T.K) *
        ‖tailFormBase T cut (tailActualLowProjection T hT cut u)‖ ^ 2 := by
  have hε : 0 ≤ 5 * tailSmoothStepConstant * T.Λ / T.K :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) tailSmoothStepConstant_pos.le)
      hT.2.2.1.le) (lt_trans zero_lt_one hT.2.2.2.2.2.2.1).le
  exact tailLowProjection_energy_bound (tailNormalizedHat_finite_bound T hT cut)
    (tailFormBase T cut) (tailLowAnalysis T hT cut)
    (tailNormalizedHat_analysis T hT cut) hε
    (norm_tailLowAnalysis_le T hT cut) (tailFormGradient T cut)
    (tailNormalizedHat_finite_gradient_sq T hT cut) u

theorem tailActualLowProjection_high_energy (T : DeepTailData)
    (hT : DeepTailHypotheses T) (cut : ℝ) (hcut : TailAdmissibleCut T cut)
    (u : tailGradientSpace T cut) :
    T.Λ * ‖tailFormBase T cut (u - tailActualLowProjection T hT cut u)‖ ^ 2 ≤
      5 * T.η * ‖tailFormGradient T cut (u - tailActualLowProjection T hT cut u)‖ ^ 2 :=
  tail_closed_high_norm_bound hT (tailAdmissibleCut_le_endpoint hT hcut)
    (tailActualLowProjection T hT cut)
    (tailActualLowProjection_preserves_core T hT cut (tailAdmissibleCut_le_endpoint hT hcut))
    (fun u n hn => tailActualLowProjection_high_means T hT cut hcut u n hn) u

end ContinuousFlexibility.Radial
