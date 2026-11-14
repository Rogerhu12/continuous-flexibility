module

public import ContinuousFlexibility.Analysis.PolynomialJetComposition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Linear operations on component-power jet bounds

These estimates retain the original functions and ordinary Fréchet
derivatives. In particular the product with a coordinate projection only
requires positive-order jets, so unbounded circle lifts are allowed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem norm_iteratedFDeriv_linear_of_pos
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (n : ℕ) (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have heq : fderiv ℝ L = fun _ : E => L := funext fun _ => L.fderiv
  rw [heq]
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ k =>
    simp only [Nat.succ_eq_add_one, iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact norm_nonneg L

theorem norm_iteratedFDeriv_clm_left_polynomial_bound
    {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : ι → ℝ) (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ι → E → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (L : F →L[ℝ] G) (n : ℕ)
    (hbound : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => L (f i y)) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hbound
  refine ⟨‖L‖ * A, P, mul_nonneg (norm_nonneg _) hA, hP, fun i x hx => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left
    ((hf i).contDiffAt ((hU i).mem_nhds hx)) (n := n) (by simp)
  have h' : ‖iteratedFDeriv ℝ n (fun y => L (f i y)) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ n (f i) x‖ := by
    simpa only [Function.comp_def] using h
  exact h'.trans ((mul_le_mul_of_nonneg_left (hb i x hx) (norm_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm)

theorem norm_iteratedFDeriv_add_polynomial_bound
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f g : ι → E → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i)) (n : ℕ)
    (hfb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * W i ^ P)
    (hgb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (g i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => f i y + g i y) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hfb
  obtain ⟨B, Q, hB, hQ, hc⟩ := hgb
  refine ⟨A + B, P + Q, add_nonneg hA hB, add_nonneg hP hQ, fun i x hx => ?_⟩
  rw [fun_iteratedFDeriv_add_apply
    (((hf i).contDiffAt ((hU i).mem_nhds hx)).of_le (by simp))
    (((hg i).contDiffAt ((hU i).mem_nhds hx)).of_le (by simp))]
  have ha' : A * W i ^ P ≤ A * W i ^ (P + Q) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_right hQ)) hA
  have hb' : B * W i ^ Q ≤ B * W i ^ (P + Q) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_left hP)) hB
  exact (norm_add_le _ _).trans ((add_le_add (hb i x hx) (hc i x hx)).trans
    ((add_le_add ha' hb').trans_eq (add_mul _ _ _).symm))

theorem norm_iteratedFDeriv_fderiv_apply_polynomial_bound
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : ι → ℝ) (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ι → E → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (v : E) (n : ℕ)
    (hbound : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ (n + 1) (f i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (f i) y v) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hbound
  refine ⟨‖v‖ * A, P, mul_nonneg (norm_nonneg _) hA, hP, fun i x hx => ?_⟩
  have hd := (hf i).fderiv_of_isOpen (hU i) (m := ∞) (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const
    (hd.contDiffAt ((hU i).mem_nhds hx)) (c := v) (n := n) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hb i x hx) (norm_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm)

theorem norm_iteratedFDeriv_coordinate_graph_polynomial_bound
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set (ℝ × ℝ)) (hU : ∀ i, IsOpen (U i))
    (g : ι → (ℝ × ℝ) → ℝ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i)) (n : ℕ) (hn : 1 ≤ n)
    (hbound : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (g i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => (y.1, g i y)) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hbound
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  refine ⟨‖L‖ + A, P, add_nonneg (norm_nonneg _) hA, hP, fun i x hx => ?_⟩
  rw [iteratedFDeriv_prodMk (contDiffAt_fst : ContDiffAt ℝ ∞ Prod.fst x)
    ((hg i).contDiffAt ((hU i).mem_nhds hx)) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  have hf : ‖iteratedFDeriv ℝ n (fun y : ℝ × ℝ => y.1) x‖ ≤ ‖L‖ * W i ^ P := by
    exact (norm_iteratedFDeriv_linear_of_pos L n hn x).trans
      (by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (Real.one_le_rpow (hW i) hP) (norm_nonneg L)))
  have hsum : ‖L‖ * W i ^ P + A * W i ^ P = (‖L‖ + A) * W i ^ P :=
    (add_mul _ _ _).symm
  have hp₁ : 0 ≤ ‖L‖ * W i ^ P := mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  have hp₂ : 0 ≤ A * W i ^ P := mul_nonneg hA
    (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  exact (max_le_max hf (hb i x hx)).trans
    ((max_le (le_add_of_nonneg_right hp₂) (le_add_of_nonneg_left hp₁)).trans_eq hsum)

theorem norm_iteratedFDeriv_scalar_coordinate_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (L : E →L[ℝ] ℝ) (n : ℕ)
    (hbound : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i t, |iteratedDeriv k (f i) t| ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ n (fun q => f i (L q)) p‖ ≤ A * W i ^ P := by
  apply norm_iteratedFDeriv_comp_polynomial_bound W hW U (fun _ => univ)
    hU (fun _ => isOpen_univ) (fun _ => L) f
    (fun _ => L.contDiff.contDiffOn) (fun i => (hf i).contDiffOn)
    (fun _ _ _ => mem_univ _) n
  · intro k hk
    obtain ⟨A, P, hA, hP, hb⟩ := hbound k hk
    refine ⟨A, P, hA, hP, fun i p _ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hb i (L p)
  · intro k hk _
    refine ⟨‖L‖, 0, norm_nonneg _, le_rfl, fun i p _ => ?_⟩
    simpa only [Real.rpow_zero, mul_one] using norm_iteratedFDeriv_linear_of_pos L k hk p

end ContinuousFlexibility.Analysis
