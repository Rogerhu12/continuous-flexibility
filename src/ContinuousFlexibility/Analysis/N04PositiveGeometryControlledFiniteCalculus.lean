module

public import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
public import ContinuousFlexibility.Analysis.PlanarInverseDerivativeBound
public import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
public import ContinuousFlexibility.Analysis.OneHighCompositionJets
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite ordinary calculus with uniform polynomial costs

Only genuine forward jets and genuine inverse germs enter these estimates.
The coefficients and powers are chosen before every map, point and numerical
envelope. Zeroth angular lift values are never bounded.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A reciprocal determinant bound and positive forward jets control the
whole finite prefix of the genuine planar inverse. -/
theorem n04PositiveGeometry_exists_planarInverse_prefix_polynomial (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, ∀ {M : ℝ}, 1 ≤ M →
      ∀ F G : PolarPoint → PolarPoint, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ F (G x) → ContDiffAt ℝ ∞ G x →
      F ∘ G =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) →
      G ∘ F =ᶠ[𝓝 (G x)] (id : PolarPoint → PolarPoint) →
      planeJacobian F (G x) ≠ 0 → |planeJacobian F (G x)|⁻¹ ≤ M →
      (∀ k, 1 ≤ k → k ≤ max 1 N → ‖iteratedFDeriv ℝ k F (G x)‖ ≤ M) →
      ∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k G x‖ ≤ C * M ^ degree := by
  choose C hC d hbound using fun j =>
    exists_nonlinearInverse_finiteJet_polynomial_envelope
      (E := PolarPoint) (F := PolarPoint) j
  let K : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), C j * 2 ^ d j
  let D : ℕ := ∑ j ∈ Finset.range (N + 1), 2 * d j
  have hcoef (j : ℕ) : 0 ≤ C j * 2 ^ d j :=
    mul_nonneg (zero_le_one.trans (hC j)) (pow_nonneg (by norm_num) _)
  have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hcoef j)
  refine ⟨K, hK, D, ?_⟩
  intro M hM F G x hF hG hright hleft hJne hJinv hraw k hk hkN
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM2 : M ≤ M ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hM (by decide : 1 ≤ 2)
  have hR : 1 ≤ 2 * M ^ 2 := by linarith
  have hMR : M ≤ 2 * M ^ 2 := by linarith
  have hFx : F (G x) = x := hright.eq_of_nhds
  have hFd := hF.differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G (F (G x)) := by
    rw [hFx]
    exact hG.differentiableAt (by simp)
  let L : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ G x
  have hL : L.comp (fderiv ℝ F (G x)) = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = (fderiv ℝ G (F (G x))).comp (fderiv ℝ F (G x)) := by rw [hFx]
      _ = fderiv ℝ (G ∘ F) (G x) := (fderiv_comp (G x) hGd hFd).symm
      _ = fderiv ℝ (id : PolarPoint → PolarPoint) (G x) := hleft.fderiv_eq
      _ = _ := by rw [fderiv_id]
  have hfirst : ‖fderiv ℝ F (G x)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using hraw 1 le_rfl (le_max_left _ _)
  have hcolumn (v : PolarPoint) (hv : ‖v‖ ≤ 1) :
      ‖fderiv ℝ F (G x) v‖ ≤ M :=
    ((fderiv ℝ F (G x)).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans
        (by simpa only [mul_one] using hfirst))
  have hcolR := hcolumn (1, 0) (by norm_num [Prod.norm_def])
  have hcolT := hcolumn (0, 1) (by norm_num [Prod.norm_def])
  have h11 : |(fderiv ℝ F (G x) (1, 0)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolR
  have h12 : |(fderiv ℝ F (G x) (0, 1)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolT
  have h21 : |(fderiv ℝ F (G x) (1, 0)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolR
  have h22 : |(fderiv ℝ F (G x) (0, 1)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolT
  have hLbound : ‖L‖ ≤ 2 * M ^ 2 := by
    have hi := fderiv_inverse_norm_le_of_germ hFd hGd hleft
      (abs_pos.mpr hJne) le_rfl h11 h12 h21 h22
    have hi' : ‖L‖ ≤ (2 * M) * |planeJacobian F (G x)|⁻¹ := by
      simpa only [L, hFx, div_eq_mul_inv] using hi
    exact hi'.trans ((mul_le_mul_of_nonneg_left hJinv (by positivity)).trans_eq (by ring))
  have hi := hbound (k - 1) hR F G x hF hG hright L hL hLbound
    (fun j hj hjk => (hraw (j + 1) (by omega)
      ((by omega : j + 1 ≤ N).trans (le_max_right _ _))).trans hMR)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk'] at hi
  have hmem : k - 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hCK : C (k - 1) * 2 ^ d (k - 1) ≤ K :=
    (Finset.single_le_sum (fun j _ => hcoef j) hmem).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdD : 2 * d (k - 1) ≤ D :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (2 * d j)) hmem
  calc
    _ ≤ C (k - 1) * (2 * M ^ 2) ^ d (k - 1) := hi
    _ = (C (k - 1) * 2 ^ d (k - 1)) * M ^ (2 * d (k - 1)) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ K * M ^ D := mul_le_mul hCK (pow_le_pow_right₀ hM hdD)
      (pow_nonneg hM0 _) (zero_le_one.trans hK)

/-- Positive ordinary jets of a composition have a universal finite
polynomial envelope; no value bound of the inner map is used. -/
theorem n04PositiveGeometry_exists_composition_prefix_polynomial
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M →
      ∀ f : Y → Z, ∀ g : X → Y, ∀ x : X,
      ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
      (∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k f (g x)‖ ≤ M) →
      (∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k g x‖ ≤ M) →
      ∀ k, 1 ≤ k → k ≤ N →
        ‖iteratedFDeriv ℝ k (f ∘ g) x‖ ≤ C * M ^ (N + 1) := by
  let C : ℝ := 1 + ∑ k ∈ Finset.range (N + 1),
    (Fintype.card (OrderedFinpartition k) : ℝ)
  have hC : 1 ≤ C :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro M hM f g x hf hg hfj hgj k hk hkN
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hterm (π : OrderedFinpartition k) :
      ‖iteratedFDeriv ℝ π.length f (g x)‖ *
        ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g x‖ ≤ M ^ (k + 1) := by
    have hp : (∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g x‖) ≤ M ^ k := by
      calc
        _ ≤ ∏ _j : Fin π.length, M := Finset.prod_le_prod₀
          (fun _ _ => norm_nonneg _)
          (fun j _ => hgj (π.partSize j) (π.partSize_pos j) ((π.partSize_le j).trans hkN))
        _ = M ^ π.length := by simp
        _ ≤ M ^ k := pow_le_pow_right₀ hM π.length_le
    exact (mul_le_mul (hfj π.length (π.length_pos (by omega)) (π.length_le.trans hkN))
      hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0).trans_eq (by ring)
  have hcard : (Fintype.card (OrderedFinpartition k) : ℝ) ≤ C :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg
      (Fintype.card (OrderedFinpartition j)))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN))).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ ∑ π : OrderedFinpartition k, ‖iteratedFDeriv ℝ π.length f (g x)‖ *
        ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g x‖ :=
      norm_iteratedFDeriv_comp_le_partition_sum hf hg k
    _ ≤ ∑ _π : OrderedFinpartition k, M ^ (k + 1) :=
      Finset.sum_le_sum fun π _ => hterm π
    _ = (Fintype.card (OrderedFinpartition k) : ℝ) * M ^ (k + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ C * M ^ (N + 1) := mul_le_mul hcard
      (pow_le_pow_right₀ hM (Nat.add_le_add_right hkN 1))
      (pow_nonneg hM0 _) (zero_le_one.trans hC)

/-- The scalar product estimate includes its actual zeroth-order value. -/
theorem n04PositiveGeometry_product_prefix_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {N : ℕ} {M : ℝ} (hM : 0 ≤ M) {f g : X → ℝ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hfj : ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k f x‖ ≤ M)
    (hgj : ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k g x‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ N * M ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k - j) g x‖ :=
      norm_iteratedFDeriv_mul_le_at hf hg k
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hb := mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj j (hjk.trans hk)) (Nat.cast_nonneg (k.choose j)))
        (hgj (k - j) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hM)
      exact hb.trans_eq (by ring)
    _ = (2 : ℝ) ^ k * M ^ 2 := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2 : ℝ) ^ N * M ^ 2 := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (sq_nonneg M)

/-- Fixed polynomial operations on a sample envelope remain one sample
envelope, with the constant selected before the sample. -/
theorem n04PositiveGeometry_polynomial_sample_pack (C A : ℝ) (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ E : ℝ, 1 ≤ E →
      C * (A * E ^ A) ^ d ≤ B * E ^ B := by
  obtain ⟨B, hB, hbound⟩ := coefficientEnvelope_pack (C * A ^ d) (A * (d : ℝ))
  refine ⟨B, hB, ?_⟩
  intro E hE
  calc
    _ = (C * A ^ d) * E ^ (A * (d : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
      ring
    _ ≤ B * E ^ B := hbound E hE

end ContinuousFlexibility.Analysis
