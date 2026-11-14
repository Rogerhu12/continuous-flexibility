module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Homogeneous normalization of local multilinear estimates

A bound on a low-seminorm ball for a multilinear map gives the one-high-factor
bound globally. Adding a positive real `δ` before rescaling handles the kernels
of the low seminorm; passing to `δ = 0` is an actual continuous limit.
The explicit normalization constant depends only on the arity, radius and
original bound, so the result is uniform in families of multilinear maps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The homogeneous expression obtained from a local affine growth bound. -/
def multilinearTameSize (low high : Seminorm ℝ E) (k : ℕ)
    (a : ℝ) (v : Fin k → E) : ℝ :=
  a * ∏ i, low (v i) + ∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, low (v j)

theorem multilinearTameSize_nonneg (low high : Seminorm ℝ E) (k : ℕ)
    {a : ℝ} (ha : 0 ≤ a) (v : Fin k → E) :
    0 ≤ multilinearTameSize low high k a v := by
  unfold multilinearTameSize
  positivity

/-- On the unit low-seminorm polydisc the homogeneous size is at most affine growth. -/
theorem multilinearTameSize_le_affine (low high : Seminorm ℝ E) (k : ℕ)
    {a : ℝ} (ha : 0 ≤ a) (v : Fin k → E) (hv : ∀ i, low (v i) ≤ 1) :
    multilinearTameSize low high k a v ≤ a + ∑ i, high (v i) := by
  unfold multilinearTameSize
  apply add_le_add
  · calc
      a * ∏ i, low (v i) ≤ a * 1 := mul_le_mul_of_nonneg_left
        (Finset.prod_le_one₀ (fun i _ => apply_nonneg _ _) (fun i _ => hv i)) ha
      _ = a := mul_one a
  · apply Finset.sum_le_sum
    intro i _
    calc
      high (v i) * ∏ j ∈ Finset.univ.erase i, low (v j) ≤ high (v i) * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun j _ => apply_nonneg _ _) (fun j _ => hv j))
          (apply_nonneg _ _)
      _ = high (v i) := mul_one _

/-- Unit-ball normalization, with exactly the original constant.
No norm or separation assumption on the low seminorm is needed. -/
theorem multilinearMap_bound_of_unitBall {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin k => E) F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ v : Fin k → E, (∀ i, low (v i) < 1) →
      q (A v) ≤ C * (a + ∑ i, high (v i))) :
    ∀ v : Fin k → E, q (A v) ≤ C * multilinearTameSize low high k a v := by
  intro v
  have hδ : ∀ δ : ℝ, 0 < δ → q (A v) ≤ C *
      (a * ∏ i, (low (v i) + δ) +
        ∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, (low (v j) + δ)) := by
    intro δ hδ
    let y : Fin k → ℝ := fun i => low (v i) + δ
    let w : Fin k → E := fun i => (y i)⁻¹ • v i
    have hy (i : Fin k) : 0 < y i := add_pos_of_nonneg_of_pos (apply_nonneg _ _) hδ
    have hyne (i : Fin k) : y i ≠ 0 := ne_of_gt (hy i)
    have hw (i : Fin k) : low (w i) < 1 := by
      dsimp [w]
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hy i)),
        inv_mul_eq_div]
      apply (div_lt_one (hy i)).mpr
      exact lt_add_of_pos_right _ hδ
    have hhigh (i : Fin k) : high (w i) = (y i)⁻¹ * high (v i) := by
      dsimp [w]
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hy i))]
    have hvec : (fun i => y i • w i) = v := by
      funext i
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ (hyne i), one_smul]
    have hscale := A.map_smul_univ y w
    rw [hvec] at hscale
    have hprod : 0 < ∏ i, y i := Finset.prod_pos (fun i _ => hy i)
    have heq : q (A v) = (∏ i, y i) * q (A w) := by
      rw [hscale, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hprod]
    have hterm (i : Fin k) :
        (∏ j, y j) * ((y i)⁻¹ * high (v i)) =
          high (v i) * ∏ j ∈ Finset.univ.erase i, y j := by
      rw [← Finset.mul_prod_erase _ y (Finset.mem_univ i)]
      calc
        _ = (y i * (y i)⁻¹) * (high (v i) * ∏ j ∈ Finset.univ.erase i, y j) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (hyne i), one_mul]
    calc
      q (A v) = (∏ i, y i) * q (A w) := heq
      _ ≤ (∏ i, y i) * (C * (a + ∑ i, high (w i))) :=
        mul_le_mul_of_nonneg_left (hlocal w hw) hprod.le
      _ = C * (a * ∏ i, y i + ∑ i, (∏ j, y j) * ((y i)⁻¹ * high (v i))) := by
        simp_rw [hhigh]
        rw [← Finset.mul_sum]
        ring
      _ = C * (a * ∏ i, y i + ∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, y j) := by
        simp_rw [hterm]
      _ = _ := rfl
  let bound : ℝ → ℝ := fun δ => C *
    (a * ∏ i, (low (v i) + δ) +
      ∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, (low (v j) + δ))
  have hprodCont (s : Finset (Fin k)) :
      Continuous (fun δ : ℝ => ∏ i ∈ s, (low (v i) + δ)) :=
    continuous_finsetProd s (fun _ _ => continuous_const.add continuous_id)
  have hsumCont : Continuous (fun δ : ℝ =>
      ∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, (low (v j) + δ)) :=
    continuous_finsetSum _ (fun i _ => (hprodCont _).const_mul _)
  have hcont : Continuous bound := (((hprodCont _).const_mul a).add hsumCont).const_mul C
  have hlim : Tendsto bound (𝓝[>] (0 : ℝ))
      (𝓝 (C * multilinearTameSize low high k a v)) := by
    have hzero : bound 0 = C * multilinearTameSize low high k a v := by
      simp only [bound, multilinearTameSize, add_zero]
    rw [← hzero]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with δ hpos
  exact hδ δ hpos

/-- The continuous version is the same algebraic normalization argument. -/
theorem multilinear_bound_of_unitBall {k : ℕ}
    (A : E [×k]→L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ v : Fin k → E, (∀ i, low (v i) < 1) →
      q (A v) ≤ C * (a + ∑ i, high (v i))) :
    ∀ v : Fin k → E, q (A v) ≤ C * multilinearTameSize low high k a v :=
  multilinearMap_bound_of_unitBall A.toMultilinearMap q low high hC hlocal

/-- The constant is uniform in the affine term and in the multilinear map. -/
def multilinearNormalizationConstant (k : ℕ) (ε C : ℝ) : ℝ :=
  C / (min (ε / 2) 1) ^ k

theorem multilinearNormalizationConstant_nonneg (k : ℕ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) : 0 ≤ multilinearNormalizationConstant k ε C := by
  unfold multilinearNormalizationConstant
  positivity

variable [ContinuousConstSMul ℝ F]

/-- Local affine growth on any positive low-seminorm ball implies the global
one-high-factor bound. The displayed constant is independent of `a`, `A`, and `v`. -/
theorem multilinearMap_oneHighFactor_of_local {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin k => E) F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {ε C a : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hlocal : ∀ v : Fin k → E, (∀ i, low (v i) < ε) →
      q (A v) ≤ C * (a + ∑ i, high (v i))) :
    ∀ v : Fin k → E, q (A v) ≤
      multilinearNormalizationConstant k ε C * multilinearTameSize low high k a v := by
  let α : ℝ := min (ε / 2) 1
  have hα : 0 < α := lt_min (half_pos hε) zero_lt_one
  have hα1 : α ≤ 1 := min_le_right _ _
  have hαε : α < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  let A' : MultilinearMap ℝ (fun _ : Fin k => E) F := (α ^ k) • A
  have hscale (v : Fin k → E) : A' v = A (fun i => α • v i) := by
    rw [A.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hunit : ∀ v : Fin k → E, (∀ i, low (v i) < 1) →
      q (A' v) ≤ C * (a + ∑ i, high (v i)) := by
    intro v hv
    have hsmall (i : Fin k) : low (α • v i) < ε := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hα]
      exact (mul_lt_mul_of_pos_left (hv i) hα).trans_le (by simpa using hαε.le)
    have hh (i : Fin k) : high (α • v i) ≤ high (v i) := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hα]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hα1 (apply_nonneg _ _)
    rw [hscale]
    exact (hlocal _ hsmall).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl a) (Finset.sum_le_sum (fun i _ => hh i))) hC)
  have hglobal := multilinearMap_bound_of_unitBall A' q low high hC hunit
  intro v
  have hpow : 0 < α ^ k := pow_pos hα _
  have hq : q (A' v) = α ^ k * q (A v) := by
    change q ((α ^ k) • A v) = _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hpow]
  have h := hglobal v
  rw [hq] at h
  change q (A v) ≤ (C / α ^ k) * multilinearTameSize low high k a v
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpow).mpr
  simpa only [mul_comm] using h

/-- Continuous multilinear maps inherit the algebraic local normalization. -/
theorem multilinear_oneHighFactor_of_local {k : ℕ}
    (A : E [×k]→L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {ε C a : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hlocal : ∀ v : Fin k → E, (∀ i, low (v i) < ε) →
      q (A v) ≤ C * (a + ∑ i, high (v i))) :
    ∀ v : Fin k → E, q (A v) ≤
      multilinearNormalizationConstant k ε C * multilinearTameSize low high k a v :=
  multilinearMap_oneHighFactor_of_local A.toMultilinearMap q low high hε hC hlocal

end ContinuousFlexibility.Analysis
