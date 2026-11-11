import ContinuousFlexibility.Analysis.AngularThreeLines
import ContinuousFlexibility.Analysis.AngularFrequency
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Weighted interpolation on the full angular Hilbert sum

The finite projection estimate is passed to the full weighted domains.
Both the input and output cutoffs tend to infinity in one sequence.  The
output converges coefficientwise, and the `lp` Fatou lemmas supply both
weighted-domain membership and the norm estimate.  No bound at an
intermediate order, nor any invariance of cutoff subspaces, is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped ENNReal Topology

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

/-- The finite three-lines estimate expressed using real diagonal weights. -/
theorem angular_three_lines_finite_weighted (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    {C : ℝ} (hC : 0 ≤ C) (hzero : ‖K‖ ≤ C)
    (hone : ∀ (s t : Finset ℕ) (v : lp E 2),
      ‖finiteDiagonal s (fun n => (a n : ℂ))
        (K (finiteDiagonal t (fun _ => 1) v))‖ ≤
      C * ‖finiteDiagonal t (fun n => (b n : ℂ)) v‖)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta' : theta ≤ 1)
    (s t : Finset ℕ) (v : lp E 2) :
    ‖finiteDiagonal s (fun n => ((a n ^ theta : ℝ) : ℂ))
        (K (finiteDiagonal t (fun _ => 1) v))‖ ≤
      C * ‖finiteDiagonal t (fun n => ((b n ^ theta : ℝ) : ℂ)) v‖ := by
  let x := finiteDiagonal t (fun n => ((b n ^ theta : ℝ) : ℂ)) v
  have hinput : finiteDiagonal t (fun n => (b n : ℂ) ^ (-(theta : ℂ))) x =
      finiteDiagonal t (fun _ => 1) v := by
    dsimp only [x]
    rw [finiteDiagonal_comp]
    apply congrArg (fun c : ℕ → ℂ => finiteDiagonal t c v)
    funext n
    rw [Complex.ofReal_cpow (hb n).le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hb n).ne'),
      neg_add_cancel, Complex.cpow_zero]
  have houtput : (fun n => (a n : ℂ) ^ (theta : ℂ)) =
      (fun n => ((a n ^ theta : ℝ) : ℂ)) :=
    funext (fun n => (Complex.ofReal_cpow (ha n).le theta).symm)
  have h := angular_three_lines_finite K a b ha hb hC hzero hone
    htheta htheta' s t x
  unfold angularInterpolationFamily at h
  rw [hinput, houtput] at h
  simpa only [x, finiteDiagonal_project] using h

/-- Truncation is contractive in every weighted domain. -/
theorem finiteDiagonal_weight_norm_le (s : Finset ℕ) (w : ℕ → ℝ) (v : lp E 2)
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    ‖finiteDiagonal s (fun n => (w n : ℂ)) v‖ ≤
      angularWeightNorm (𝕜 := ℂ) w v := by
  have heq : finiteDiagonal s (fun n => (w n : ℂ)) v =
      finiteDiagonal s (fun _ => 1) (angularMultiplierVector w v hv) := by
    ext n
    by_cases hn : n ∈ s <;>
      simp only [finiteDiagonal_apply, hn, if_true, if_false,
        angularMultiplierVector_apply, RCLike.ofReal_eq_complex_ofReal, one_smul]
  rw [heq, ← norm_angularMultiplierVector w v hv]
  exact finiteDiagonal_projection_norm_le s _

/-- Every finite spectral projection belongs to every weighted domain. -/
theorem memAngularWeight_finiteDiagonal (s : Finset ℕ) (w : ℕ → ℝ) (v : lp E 2) :
    MemAngularWeight (𝕜 := ℂ) w (finiteDiagonal s (fun _ => 1) v) := by
  have heq : (fun n => (w n : ℂ) • finiteDiagonal s (fun _ => 1) v n) =
      (finiteDiagonal s (fun n => (w n : ℂ)) v : ∀ n, E n) := by
    funext n
    by_cases hn : n ∈ s <;>
      simp only [finiteDiagonal_apply, hn, if_true, if_false, one_smul, smul_zero]
  unfold MemAngularWeight
  simpa only [RCLike.ofReal_eq_complex_ofReal, ← heq] using
    lp.memℓp (finiteDiagonal s (fun n => (w n : ℂ)) v)

theorem angularWeightNorm_finiteDiagonal (s : Finset ℕ) (w : ℕ → ℝ) (v : lp E 2) :
    angularWeightNorm (𝕜 := ℂ) w (finiteDiagonal s (fun _ => 1) v) =
      ‖finiteDiagonal s (fun n => (w n : ℂ)) v‖ := by
  rw [← norm_angularMultiplierVector _ _ (memAngularWeight_finiteDiagonal s w v)]
  congr 1
  ext n
  by_cases hn : n ∈ s <;>
    simp only [finiteDiagonal_apply, angularMultiplierVector_apply,
      RCLike.ofReal_eq_complex_ofReal, hn, if_true, if_false, one_smul, smul_zero]

/-- The canonical finite spectral projections converge in the base norm. -/
theorem tendsto_finiteDiagonal_projection (v : lp E 2) :
    Tendsto (fun N : ℕ => finiteDiagonal (Finset.range N) (fun _ => 1) v)
      atTop (𝓝 v) := by
  simpa only [finiteDiagonal, one_smul] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v).tendsto_sum_nat

/-- Simultaneous finite input and output projections converge coefficientwise
after any fixed diagonal weight. -/
theorem tendsto_finiteDiagonal_weighted_output (K : lp E 2 →L[ℂ] lp E 2)
    (w : ℕ → ℝ) (v : lp E 2) :
    Tendsto (fun N : ℕ =>
      (finiteDiagonal (Finset.range N) (fun n => (w n : ℂ))
        (K (finiteDiagonal (Finset.range N) (fun _ => 1) v)) : ∀ n, E n))
      atTop (𝓝 (fun n => (w n : ℂ) • K v n)) := by
  have hK := K.continuous.continuousAt.tendsto.comp (tendsto_finiteDiagonal_projection v)
  apply tendsto_pi_nhds.mpr
  intro n
  have hn : Tendsto
      (fun N : ℕ => K (finiteDiagonal (Finset.range N) (fun _ => 1) v) n)
      atTop (𝓝 (K v n)) :=
    (lp.lipschitzWith_one_eval 2 n).continuous.continuousAt.tendsto.comp hK
  apply (hn.const_smul (w n : ℂ)).congr'
  filter_upwards [eventually_gt_atTop n] with N hN
  simp only [finiteDiagonal_apply, Finset.mem_range.mpr hN, if_true]

/-- Full weighted three-lines interpolation, including the output domain.
The endpoint hypothesis uses finite projections only; the conclusion holds
for every vector in the indicated weighted domain. -/
theorem angular_three_lines_weighted (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    {C : ℝ} (hC : 0 ≤ C) (hzero : ‖K‖ ≤ C)
    (hone : ∀ (s t : Finset ℕ) (v : lp E 2),
      ‖finiteDiagonal s (fun n => (a n : ℂ))
        (K (finiteDiagonal t (fun _ => 1) v))‖ ≤
      C * ‖finiteDiagonal t (fun n => (b n : ℂ)) v‖)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta' : theta ≤ 1)
    (v : lp E 2) (hv : MemAngularWeight (𝕜 := ℂ) (fun n => b n ^ theta) v) :
    MemAngularWeight (𝕜 := ℂ) (fun n => a n ^ theta) (K v) ∧
      angularWeightNorm (𝕜 := ℂ) (fun n => a n ^ theta) (K v) ≤
        C * angularWeightNorm (𝕜 := ℂ) (fun n => b n ^ theta) v := by
  let F : ℕ → lp E 2 := fun N =>
    finiteDiagonal (Finset.range N) (fun n => ((a n ^ theta : ℝ) : ℂ))
      (K (finiteDiagonal (Finset.range N) (fun _ => 1) v))
  let D := C * angularWeightNorm (𝕜 := ℂ) (fun n => b n ^ theta) v
  have hbound : ∀ N, ‖F N‖ ≤ D := by
    intro N
    exact (angular_three_lines_finite_weighted K a b ha hb hC hzero hone
      htheta htheta' (Finset.range N) (Finset.range N) v).trans
        (mul_le_mul_of_nonneg_left (finiteDiagonal_weight_norm_le _ _ v hv) hC)
  have hbounded : Bornology.IsBounded (Set.range F) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨D, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hbound N
  have hlim : Tendsto (fun N => (F N : ∀ n, E n)) atTop
      (𝓝 (fun n => ((a n ^ theta : ℝ) : ℂ) • K v n)) :=
    tendsto_finiteDiagonal_weighted_output K (fun n => a n ^ theta) v
  have hmem : MemAngularWeight (𝕜 := ℂ) (fun n => a n ^ theta) (K v) :=
    lp.memℓp_of_tendsto hbounded hlim
  refine ⟨hmem, ?_⟩
  rw [← norm_angularMultiplierVector _ _ hmem]
  exact lp.norm_le_of_tendsto (Eventually.of_forall hbound) hlim

/-- A full-domain endpoint bound implies all intermediate weighted bounds.
This is the usual operator interpolation statement, with the output-domain
assertion included explicitly. -/
theorem angular_three_lines (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    {C : ℝ} (hC : 0 ≤ C) (hzero : ‖K‖ ≤ C)
    (hone : ∀ v : lp E 2, MemAngularWeight (𝕜 := ℂ) b v →
      MemAngularWeight (𝕜 := ℂ) a (K v) ∧
      angularWeightNorm (𝕜 := ℂ) a (K v) ≤ C * angularWeightNorm (𝕜 := ℂ) b v)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta' : theta ≤ 1)
    (v : lp E 2) (hv : MemAngularWeight (𝕜 := ℂ) (fun n => b n ^ theta) v) :
    MemAngularWeight (𝕜 := ℂ) (fun n => a n ^ theta) (K v) ∧
      angularWeightNorm (𝕜 := ℂ) (fun n => a n ^ theta) (K v) ≤
        C * angularWeightNorm (𝕜 := ℂ) (fun n => b n ^ theta) v := by
  apply angular_three_lines_weighted K a b ha hb hC hzero _ htheta htheta' v hv
  intro s t u
  obtain ⟨hmem, hbound⟩ := hone (finiteDiagonal t (fun _ => 1) u)
    (memAngularWeight_finiteDiagonal t b u)
  calc
    _ ≤ angularWeightNorm (𝕜 := ℂ) a (K (finiteDiagonal t (fun _ => 1) u)) :=
      finiteDiagonal_weight_norm_le s a _ hmem
    _ ≤ C * angularWeightNorm (𝕜 := ℂ) b (finiteDiagonal t (fun _ => 1) u) := hbound
    _ = C * ‖finiteDiagonal t (fun n => (b n : ℂ)) u‖ := by
      rw [angularWeightNorm_finiteDiagonal]

end ContinuousFlexibility.Analysis
