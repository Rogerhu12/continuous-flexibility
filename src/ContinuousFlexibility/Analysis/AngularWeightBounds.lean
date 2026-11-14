module

public import ContinuousFlexibility.Analysis.AngularFrequency
public import ContinuousFlexibility.Analysis.AngularTameConstants

/-!
# Weighted Hilbert-sum inequalities for angular estimates

All comparisons are made on the full Hilbert sum with arbitrary fibers.
The domain hypotheses are explicit, including for every use of a weighted
norm defined by a square sum.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

theorem MemAngularWeight.add_weight {g h : ℕ → ℝ} {v : lp E 2}
    (hg : MemAngularWeight (𝕜 := 𝕜) g v)
    (hh : MemAngularWeight (𝕜 := 𝕜) h v) :
    MemAngularWeight (𝕜 := 𝕜) (fun n => g n + h n) v := by
  simpa only [MemAngularWeight, RCLike.ofReal_add, add_smul, Pi.add_def] using Memℓp.add hg hh

theorem MemAngularWeight.const_mul_weight {w : ℕ → ℝ} {v : lp E 2}
    (hw : MemAngularWeight (𝕜 := 𝕜) w v) (c : ℝ) :
    MemAngularWeight (𝕜 := 𝕜) (fun n => c * w n) v := by
  simpa only [MemAngularWeight, RCLike.ofReal_mul, mul_smul, Pi.smul_def] using
    Memℓp.const_smul hw (c : 𝕜)

theorem memAngularWeight_const (c : ℝ) (v : lp E 2) :
    MemAngularWeight (𝕜 := 𝕜) (fun _ => c) v :=
  (lp.memℓp v).const_smul (c : 𝕜)

theorem angularWeightNorm_const (c : ℝ) (v : lp E 2) :
    angularWeightNorm (𝕜 := 𝕜) (fun _ => c) v = |c| * ‖v‖ := by
  rw [← norm_angularMultiplierVector _ v (memAngularWeight_const c v)]
  have heq : angularMultiplierVector (𝕜 := 𝕜) (fun _ => c) v
      (memAngularWeight_const (𝕜 := 𝕜) c v) =
      (c : 𝕜) • v := by
    ext n
    simp only [angularMultiplierVector_apply, lp.coeFn_smul, Pi.smul_apply]
  rw [heq, norm_smul, RCLike.norm_ofReal]

theorem angularWeightNorm_const_mul {w : ℕ → ℝ} {v : lp E 2}
    (hw : MemAngularWeight (𝕜 := 𝕜) w v) (c : ℝ) :
    angularWeightNorm (𝕜 := 𝕜) (fun n => c * w n) v =
      |c| * angularWeightNorm (𝕜 := 𝕜) w v := by
  rw [← norm_angularMultiplierVector _ v (hw.const_mul_weight c),
    ← norm_angularMultiplierVector w v hw]
  have heq : angularMultiplierVector (fun n => c * w n) v (hw.const_mul_weight c) =
      (c : 𝕜) • angularMultiplierVector w v hw := by
    ext n
    simp only [angularMultiplierVector_apply, lp.coeFn_smul, Pi.smul_apply,
      RCLike.ofReal_mul, mul_smul]
  rw [heq, norm_smul, RCLike.norm_ofReal]

theorem angularWeightNorm_add_weight_le {g h : ℕ → ℝ} {v : lp E 2}
    (hg : MemAngularWeight (𝕜 := 𝕜) g v)
    (hh : MemAngularWeight (𝕜 := 𝕜) h v) :
    angularWeightNorm (𝕜 := 𝕜) (fun n => g n + h n) v ≤
      angularWeightNorm (𝕜 := 𝕜) g v + angularWeightNorm (𝕜 := 𝕜) h v := by
  rw [← norm_angularMultiplierVector _ v (hg.add_weight hh),
    ← norm_angularMultiplierVector g v hg, ← norm_angularMultiplierVector h v hh]
  have heq : angularMultiplierVector (fun n => g n + h n) v (hg.add_weight hh) =
      angularMultiplierVector g v hg + angularMultiplierVector h v hh := by
    ext n
    simp only [angularMultiplierVector_apply, lp.coeFn_add, Pi.add_apply,
      RCLike.ofReal_add, add_smul]
  rw [heq]
  exact norm_add_le _ _

theorem MemAngularWeight.of_le_add {w g h : ℕ → ℝ} {v : lp E 2}
    (hg : MemAngularWeight (𝕜 := 𝕜) g v)
    (hh : MemAngularWeight (𝕜 := 𝕜) h v)
    (hw : ∀ n, |w n| ≤ g n + h n) : MemAngularWeight (𝕜 := 𝕜) w v := by
  apply (hg.add_weight hh).mono
  intro n
  exact (hw n).trans (le_abs_self _)

theorem angularWeightNorm_le_add {w g h : ℕ → ℝ} {v : lp E 2}
    (hg : MemAngularWeight (𝕜 := 𝕜) g v)
    (hh : MemAngularWeight (𝕜 := 𝕜) h v)
    (hw : ∀ n, |w n| ≤ g n + h n) :
    angularWeightNorm (𝕜 := 𝕜) w v ≤
      angularWeightNorm (𝕜 := 𝕜) g v + angularWeightNorm (𝕜 := 𝕜) h v := by
  exact (angularWeightNorm_mono (hg.add_weight hh)
    (fun n => (hw n).trans (le_abs_self _))).trans (angularWeightNorm_add_weight_le hg hh)

/-- Adjacent Sobolev levels with an arbitrary positive absorption parameter. -/
theorem angularSobolevNorm_adjacent {v : lp E 2} {m : ℕ}
    (hv : MemAngularSobolev (𝕜 := 𝕜) (m + 1) v)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    angularSobolevNorm (𝕜 := 𝕜) m v ≤
      epsilon * angularSobolevNorm (𝕜 := 𝕜) (m + 1) v + epsilon⁻¹ ^ m * ‖v‖ := by
  have h := angularWeightNorm_le_add (hv.const_mul_weight epsilon)
    (memAngularWeight_const (epsilon⁻¹ ^ m) v) (w := fun n => angularWeight n ^ m)
    (fun n => by
      rw [abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) m)]
      exact angular_pow_le_epsilon_succ (angularWeight_nonneg n) hepsilon m)
  rw [angularWeightNorm_const_mul hv epsilon, angularWeightNorm_const,
    abs_of_pos hepsilon, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hepsilon.le) m)] at h
  exact h

/-- The mixed Young term is bounded by the top weight plus one linear copy
of the large coefficient. -/
theorem angularWeightNorm_mixed {v : lp E 2} {m k : ℕ}
    (hv : MemAngularSobolev (𝕜 := 𝕜) m v) (hm : 0 < m) (hk : k ≤ m)
    {A : ℝ} (hA : 0 ≤ A) :
    A ^ ((k : ℝ) / m) * angularSobolevNorm (𝕜 := 𝕜) (m - k) v ≤
      angularSobolevNorm (𝕜 := 𝕜) m v + A * ‖v‖ := by
  have hlow : MemAngularSobolev (𝕜 := 𝕜) (m - k) v := hv.of_le (Nat.sub_le _ _)
  have h := angularWeightNorm_le_add hv (memAngularWeight_const A v)
    (w := fun n => A ^ ((k : ℝ) / m) * angularWeight n ^ (m - k))
    (fun n => by
      rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hA _) (pow_nonneg (angularWeight_nonneg n) _))]
      exact angular_mixed_weight_le hA (angularWeight_nonneg n) hm hk)
  rw [angularWeightNorm_const_mul hlow _, angularWeightNorm_const,
    abs_of_nonneg (Real.rpow_nonneg hA _), abs_of_nonneg hA] at h
  exact h

end ContinuousFlexibility.Analysis
