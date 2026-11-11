import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth radial exhaustion of a canonical interval

The cutoffs are supported strictly inside the actual canonical radial
interval, lie between zero and one, and are eventually one at each
interior point. Dominated convergence therefore removes the compact
radial support from the separated Fourier tests without adding boundary
regularity to a source class.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

private def n07aAngularCutoffGap (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

private theorem n07aAngularCutoffGap_pos (k : ℕ) : 0 < n07aAngularCutoffGap k := by
  unfold n07aAngularCutoffGap
  positivity

private theorem n07aAngularCutoffGap_lt_one (k : ℕ) : n07aAngularCutoffGap k < 1 := by
  unfold n07aAngularCutoffGap
  rw [div_lt_one (by positivity : 0 < (k : ℝ) + 2)]
  linarith [Nat.cast_nonneg (α := ℝ) k]

private def n07aAngularIntervalBump (a b : ℝ) (hab : a < b) (k : ℕ) :
    ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 2 * (1 - n07aAngularCutoffGap k)
  rOut := (b - a) / 2 * (1 - n07aAngularCutoffGap k / 2)
  rIn_pos := mul_pos (by linarith) (sub_pos.mpr (n07aAngularCutoffGap_lt_one k))
  rIn_lt_rOut := by
    apply mul_lt_mul_of_pos_left
    · linarith [n07aAngularCutoffGap_pos k]
    · linarith

def n07aAngularIntervalCutoff (a b : ℝ) (hab : a < b) (k : ℕ) : ℝ → ℝ :=
  n07aAngularIntervalBump a b hab k

theorem n07aAngularIntervalCutoff_contDiff (a b : ℝ) (hab : a < b) (k : ℕ) :
    ContDiff ℝ ∞ (n07aAngularIntervalCutoff a b hab k) :=
  (n07aAngularIntervalBump a b hab k).contDiff

theorem n07aAngularIntervalCutoff_bounds (a b : ℝ) (hab : a < b) (k : ℕ) (r : ℝ) :
    n07aAngularIntervalCutoff a b hab k r ∈ Icc (0 : ℝ) 1 :=
  ⟨(n07aAngularIntervalBump a b hab k).nonneg,
    (n07aAngularIntervalBump a b hab k).le_one⟩

theorem n07aAngularIntervalCutoff_compact (a b : ℝ) (hab : a < b) (k : ℕ) :
    HasCompactSupport (n07aAngularIntervalCutoff a b hab k) :=
  (n07aAngularIntervalBump a b hab k).hasCompactSupport

theorem n07aAngularIntervalCutoff_tsupport (a b : ℝ) (hab : a < b) (k : ℕ) :
    tsupport (n07aAngularIntervalCutoff a b hab k) ⊆ Ioo a b := by
  rw [n07aAngularIntervalCutoff, (n07aAngularIntervalBump a b hab k).tsupport_eq]
  intro r hr
  have hdist := Metric.mem_closedBall.mp hr
  rw [Real.dist_eq] at hdist
  have hstrict : (n07aAngularIntervalBump a b hab k).rOut < (b - a) / 2 := by
    dsimp only [n07aAngularIntervalBump]
    have hp : 0 < (b - a) / 2 := by linarith
    nlinarith [n07aAngularCutoffGap_pos k]
  have h := abs_lt.mp (hdist.trans_lt hstrict)
  constructor <;> linarith

theorem n07aAngularIntervalCutoff_eventually_one (a b : ℝ) (hab : a < b)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    ∀ᶠ k : ℕ in atTop, n07aAngularIntervalCutoff a b hab k r = 1 := by
  have hgap : Tendsto n07aAngularCutoffGap atTop (𝓝 0) := by
    unfold n07aAngularCutoffGap
    have h := (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hin : Tendsto (fun k => (n07aAngularIntervalBump a b hab k).rIn)
      atTop (𝓝 ((b - a) / 2)) := by
    simpa only [n07aAngularIntervalBump, sub_zero, mul_one] using
      (tendsto_const_nhds (x := (b - a) / 2)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hgap)
  have hd : dist r ((a + b) / 2) < (b - a) / 2 := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  filter_upwards [hin.eventually_const_lt hd] with k hk
  exact (n07aAngularIntervalBump a b hab k).one_of_mem_closedBall
    (Metric.mem_closedBall.mpr hk.le)

variable {S : PhysicalSpacesData} {K : CanonicalData S}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact radial tests converge to the actual integral of any integrable class. -/
theorem n07aAngularIntervalCutoff_integral_tendsto (m : ℕ)
    (hm : K.left m < K.right m) {F : PolarPoint → E}
    (hF : Integrable F (canonicalMeasure S K m)) :
    Tendsto (fun k => ∫ p, n07aAngularIntervalCutoff (K.left m) (K.right m) hm k p.1 • F p
      ∂canonicalMeasure S K m) atTop (𝓝 (∫ p, F p ∂canonicalMeasure S K m)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => ‖F p‖)
  · intro k
    exact ((n07aAngularIntervalCutoff_contDiff (K.left m) (K.right m) hm k).continuous.comp
      continuous_fst).aestronglyMeasurable.smul hF.aestronglyMeasurable
  · exact hF.norm
  · intro k
    exact Eventually.of_forall (fun p => by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (n07aAngularIntervalCutoff_bounds _ _ hm k p.1).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (n07aAngularIntervalCutoff_bounds _ _ hm k p.1).2)
  · have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [n07aAngularIntervalCutoff_eventually_one _ _ hm hp.1] with k hk
    rw [hk, one_smul]

end ContinuousFlexibility.Statements
