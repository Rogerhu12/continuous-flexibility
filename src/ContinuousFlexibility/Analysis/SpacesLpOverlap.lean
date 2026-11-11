import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Bounded-overlap localization and Hilbert-space gluing

A family of scalar cutoffs with a uniformly bounded sum of squares gives
a bounded map into the Hilbert sum of the original `L²` space. Its adjoint
is the actual gluing map: on each single row it multiplies by that row's
cutoff. This construction keeps all infinite sums inside complete spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem spacesLpReal_norm_sq (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

theorem spacesMemLp_bounded_mul {χ f : α → ℝ} (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hC : ∀ x, |χ x| ≤ C) (hf : MemLp f 2 μ) :
    MemLp (fun x => χ x * f x) 2 μ := by
  apply hf.of_le_mul (c := C) (hχ.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

private def spacesLpMultiplierFun (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (spacesMemLp_bounded_mul μ hχ hC (Lp.memLp u)).toLp (fun x => χ x * u x)

private theorem spacesLpMultiplierFun_ae (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) (u : Lp ℝ 2 μ) :
    (spacesLpMultiplierFun μ χ hχ C hC u : α → ℝ) =ᵐ[μ] fun x => χ x * u x :=
  MemLp.coeFn_toLp _

/-- Multiplication by an actual bounded measurable scalar function. -/
def spacesLpMultiplier (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := spacesLpMultiplierFun μ χ hχ C hC
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [spacesLpMultiplierFun_ae μ χ hχ C hC (u + v),
          spacesLpMultiplierFun_ae μ χ hχ C hC u, spacesLpMultiplierFun_ae μ χ hχ C hC v,
          Lp.coeFn_add u v, Lp.coeFn_add (spacesLpMultiplierFun μ χ hχ C hC u)
            (spacesLpMultiplierFun μ χ hχ C hC v)] with x huv hu hv hin hout
        rw [huv, hout, hin]
        simp only [Pi.add_apply]
        rw [hu, hv]
        ring
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [spacesLpMultiplierFun_ae μ χ hχ C hC (c • u),
          spacesLpMultiplierFun_ae μ χ hχ C hC u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (spacesLpMultiplierFun μ χ hχ C hC u)] with x hcu hu hin hout
        simp only [RingHom.id_apply]
        rw [hcu, hout, hin]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        ring }
    C (fun u => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [spacesLpMultiplierFun_ae μ χ hχ C hC u] with x hx
      change ‖spacesLpMultiplierFun μ χ hχ C hC u x‖ ≤ C * ‖u x‖
      rw [hx]
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _))

theorem spacesLpMultiplier_ae (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) (u : Lp ℝ 2 μ) :
    (spacesLpMultiplier μ χ hχ C hC u : α → ℝ) =ᵐ[μ] fun x => χ x * u x :=
  spacesLpMultiplierFun_ae μ χ hχ C hC u

theorem spacesLpMultiplier_norm_le (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) (u : Lp ℝ 2 μ) :
    ‖spacesLpMultiplier μ χ hχ C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [spacesLpMultiplier_ae μ χ hχ C hC u] with x hx
  rw [hx]
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

theorem spacesLpMultiplier_inner (χ : α → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (C : ℝ) (hC : ∀ x, |χ x| ≤ C) (u v : Lp ℝ 2 μ) :
    inner ℝ (spacesLpMultiplier μ χ hχ C hC u) v =
      inner ℝ u (spacesLpMultiplier μ χ hχ C hC v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spacesLpMultiplier_ae μ χ hχ C hC u,
    spacesLpMultiplier_ae μ χ hχ C hC v] with x hu hv
  rw [hu, hv]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

section Family

variable {ι : Type*} (χ : ι → α → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
  (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ (s : Finset ι) x, ∑ i ∈ s, χ i x ^ 2 ≤ C ^ 2)

omit [MeasurableSpace α] in
include hC hbound in
private theorem spacesLpOverlap_bound_one (i : ι) (x : α) : |χ i x| ≤ C := by
  have h := hbound {i} x
  simp only [Finset.sum_singleton] at h
  exact (sq_le_sq₀ (abs_nonneg _) hC).mp (by simpa only [sq_abs] using h)

private def spacesLpOverlapRow (i : ι) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  spacesLpMultiplier μ (χ i) (hχ i) C (spacesLpOverlap_bound_one χ C hC hbound i)

private theorem spacesLpOverlap_sum_norm_sq (s : Finset ι) (u : Lp ℝ 2 μ) :
    ∑ i ∈ s, ‖spacesLpOverlapRow μ χ hχ C hC hbound i u‖ ^ 2 ≤ (C * ‖u‖) ^ 2 := by
  have hint (i : ι) : Integrable (fun x => (χ i x * u x) ^ 2) μ :=
    (spacesMemLp_bounded_mul μ (hχ i) (spacesLpOverlap_bound_one χ C hC hbound i)
      (Lp.memLp u)).integrable_sq
  calc
    (∑ i ∈ s, ‖spacesLpOverlapRow μ χ hχ C hC hbound i u‖ ^ 2) =
        ∫ x, ∑ i ∈ s, (χ i x * u x) ^ 2 ∂μ := by
      rw [integral_finsetSum s (fun i _ => hint i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [spacesLpReal_norm_sq]
      apply integral_congr_ae
      filter_upwards [spacesLpMultiplier_ae μ (χ i) (hχ i) C
        (spacesLpOverlap_bound_one χ C hC hbound i) u] with x hx
      exact congrArg (fun t : ℝ => t ^ 2) hx
    _ ≤ ∫ x, C ^ 2 * u x ^ 2 ∂μ := by
      apply integral_mono (integrable_finsetSum s (fun i _ => hint i))
        ((Lp.memLp u).integrable_sq.const_mul (C ^ 2))
      intro x
      simp only [mul_pow, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound s x) (sq_nonneg _)
    _ = (C * ‖u‖) ^ 2 := by
      rw [integral_const_mul, ← spacesLpReal_norm_sq]
      ring

private def spacesLpOverlapAnalysisFun (u : Lp ℝ 2 μ) : lp (fun _ : ι => Lp ℝ 2 μ) 2 :=
  ⟨fun i => spacesLpOverlapRow μ χ hχ C hC hbound i u,
    memℓp_gen' (C := (C * ‖u‖) ^ 2) (fun s => by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        spacesLpOverlap_sum_norm_sq μ χ hχ C hC hbound s u)⟩

private theorem spacesLpOverlapAnalysisFun_norm_le (u : Lp ℝ 2 μ) :
    ‖spacesLpOverlapAnalysisFun μ χ hχ C hC hbound u‖ ≤ C * ‖u‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (mul_nonneg hC (norm_nonneg u))
  intro s
  simpa only [spacesLpOverlapAnalysisFun, ENNReal.toReal_ofNat, Real.rpow_two] using
    spacesLpOverlap_sum_norm_sq μ χ hχ C hC hbound s u

/-- Localization into the Hilbert sum, using the actual cutoff multipliers. -/
def spacesLpOverlapAnalysis : Lp ℝ 2 μ →L[ℝ] lp (fun _ : ι => Lp ℝ 2 μ) 2 :=
  LinearMap.mkContinuous
    { toFun := spacesLpOverlapAnalysisFun μ χ hχ C hC hbound
      map_add' := by
        intro u v
        apply lp.ext
        funext i
        exact (spacesLpOverlapRow μ χ hχ C hC hbound i).map_add u v
      map_smul' := by
        intro c u
        apply lp.ext
        funext i
        exact (spacesLpOverlapRow μ χ hχ C hC hbound i).map_smul c u }
    C (spacesLpOverlapAnalysisFun_norm_le μ χ hχ C hC hbound)

theorem spacesLpOverlapAnalysis_apply (u : Lp ℝ 2 μ) (i : ι) :
    spacesLpOverlapAnalysis μ χ hχ C hC hbound u i =
      spacesLpMultiplier μ (χ i) (hχ i) C (spacesLpOverlap_bound_one χ C hC hbound i) u := rfl

theorem spacesLpOverlapAnalysis_norm_le (u : Lp ℝ 2 μ) :
    ‖spacesLpOverlapAnalysis μ χ hχ C hC hbound u‖ ≤ C * ‖u‖ :=
  spacesLpOverlapAnalysisFun_norm_le μ χ hχ C hC hbound u

/-- Hilbert-space gluing is the adjoint of localization. -/
def spacesLpOverlapSynthesis : lp (fun _ : ι => Lp ℝ 2 μ) 2 →L[ℝ] Lp ℝ 2 μ :=
  (spacesLpOverlapAnalysis μ χ hχ C hC hbound).adjoint

theorem spacesLpOverlapSynthesis_single [DecidableEq ι] (i : ι) (u : Lp ℝ 2 μ) :
    spacesLpOverlapSynthesis μ χ hχ C hC hbound (lp.single 2 i u) =
      spacesLpMultiplier μ (χ i) (hχ i) C (spacesLpOverlap_bound_one χ C hC hbound i) u := by
  apply ext_inner_right ℝ
  intro v
  rw [spacesLpOverlapSynthesis, ContinuousLinearMap.adjoint_inner_left,
    lp.inner_single_left, spacesLpOverlapAnalysis_apply]
  exact (spacesLpMultiplier_inner μ (χ i) (hχ i) C
    (spacesLpOverlap_bound_one χ C hC hbound i) u v).symm

theorem spacesLpOverlapSynthesis_norm_le (u : lp (fun _ : ι => Lp ℝ 2 μ) 2) :
    ‖spacesLpOverlapSynthesis μ χ hχ C hC hbound u‖ ≤ C * ‖u‖ := by
  have hn : ‖spacesLpOverlapSynthesis μ χ hχ C hC hbound‖ ≤ C := by
    rw [spacesLpOverlapSynthesis, LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ hC
      (spacesLpOverlapAnalysis_norm_le μ χ hχ C hC hbound)
  exact ((spacesLpOverlapSynthesis μ χ hχ C hC hbound).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg u))

end Family

end ContinuousFlexibility.Analysis
