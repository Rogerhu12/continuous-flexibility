import ContinuousFlexibility.Analysis.L2KernelExtension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Extending a kernel representation from smooth tests to all L² sources

The measure, kernel and bounded operator are fixed throughout. Smooth
compact tests in an open set of full measure are dense in the actual L²
space. Square-integrable kernel rows give continuous source pairings, so
the operator's test representation extends to every L² source.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal

/-- L² classes represented by smooth functions compactly supported in U. -/
def l2SmoothTestSubmodule (μ : Measure ℝ) (U : Set ℝ) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ U ∧ (f : ℝ → ℝ) =ᵐ[μ] φ}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero,
    by simp only [tsupport_zero, empty_subset], Lp.coeFn_zero ℝ 2 μ⟩
  add_mem' := by
    rintro f g ⟨φ, hφ, hcφ, hsφ, hf⟩ ⟨ψ, hψ, hcψ, hsψ, hg⟩
    refine ⟨φ + ψ, hφ.add hψ, hcφ.add hcψ,
      (tsupport_add φ ψ).trans (union_subset hsφ hsψ), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
    exact hx.trans (congrArg₂ (· + ·) hfx hgx)
  smul_mem' := by
    rintro a f ⟨φ, hφ, hcφ, hsφ, hf⟩
    refine ⟨fun x => a * φ x, contDiff_const.mul hφ, hcφ.mul_left,
      tsupport_mul_subset_right.trans hsφ, ?_⟩
    filter_upwards [Lp.coeFn_smul a f, hf] with x hx hfx
    simpa only [Pi.smul_apply, smul_eq_mul, hfx] using hx

/-- Density follows from the fundamental lemma for smooth tests, applied
to the orthogonal complement. No approximation theorem for a different
measure or a different function space is used. -/
theorem dense_l2SmoothTestSubmodule {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {U : Set ℝ} (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) :
    Dense (l2SmoothTestSubmodule μ U : Set (Lp ℝ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  have hz : ∀ᵐ x ∂μ, x ∈ U → f x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
    intro φ hφ hc hs
    have hm : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hc
    have hi : ⟪hm.toLp φ, f⟫_ℝ = 0 :=
      ((l2SmoothTestSubmodule μ U).mem_orthogonal f).mp hf
        (hm.toLp φ) ⟨φ, hφ, hc, hs, hm.coeFn_toLp⟩
    rw [L2.inner_def] at hi
    calc
      (∫ x, φ x • f x ∂μ) = ∫ x, ⟪(hm.toLp φ) x, f x⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hm.coeFn_toLp] with x hx
        simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial] <;> ring
      _ = 0 := hi
  apply Lp.ext
  filter_upwards [hz, hμ, Lp.coeFn_zero ℝ 2 μ] with x hx hxu hzero
  exact (hx hxu).trans hzero.symm

private theorem l2KernelRow_pairing {μ : Measure ℝ} {k : ℝ → ℝ}
    (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) :
    ⟪hk.toLp k, f⟫_ℝ = ∫ y, k y * f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hk.coeFn_toLp] with y hy
  simp only [hy, RCLike.inner_apply, conj_trivial] <;> ring

/-- A bounded L² operator known to have a fixed kernel on smooth compact
tests has that same kernel for every source. Only row-wise L² membership
is needed; no uniform row bound or all-source representation is assumed. -/
theorem l2Kernel_representation_of_smooth_tests {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (G : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (κ : ℝ → ℝ → ℝ) (hrow : ∀ᵐ x ∂μ, MemLp (κ x) 2 μ)
    (htest : ∀ (f : Lp ℝ 2 μ) (φ : ℝ → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ U → (f : ℝ → ℝ) =ᵐ[μ] φ →
      (G f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, κ x y * φ y ∂μ)
    (f : Lp ℝ 2 μ) :
    (G f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, κ x y * f y ∂μ := by
  classical
  let row : ℝ → Lp ℝ 2 μ := fun x =>
    if hx : MemLp (κ x) 2 μ then hx.toLp (κ x) else 0
  have hpair (x : ℝ) (hx : MemLp (κ x) 2 μ) (g : Lp ℝ 2 μ) :
      inner ℝ (row x) g = ∫ y, κ x y * g y ∂μ := by
    dsimp only [row]
    rw [dif_pos hx]
    exact l2KernelRow_pairing hx g
  have hrep : ∀ g ∈ l2SmoothTestSubmodule μ U,
      (G g : ℝ → ℝ) =ᵐ[μ] fun x => inner ℝ (row x) g := by
    rintro g ⟨φ, hφ, hc, hs, hφae⟩
    filter_upwards [htest g φ hφ hc hs hφae, hrow] with x hx hk
    rw [hpair x hk g]
    apply hx.trans
    apply integral_congr_ae
    filter_upwards [hφae] with y hy
    rw [hy]
  have hfull := ae_eq_row_pairing_of_dense G row
    (dense_l2SmoothTestSubmodule hU hμ) hrep f
  filter_upwards [hfull, hrow] with x hx hk
  exact hx.trans (hpair x hk f)

end ContinuousFlexibility.Analysis
