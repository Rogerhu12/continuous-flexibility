module

public import ContinuousFlexibility.Analysis.N06NuFiniteDifference
public import ContinuousFlexibility.Analysis.CylinderMixedJets
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Spatial calculus for the actual nu packet

These estimates use full Fréchet derivatives on the physical plane. In
particular a change of canonical coordinates need not preserve radial
lines. The finite nu formula is differentiated on its actual positive
discriminant segment, and the polar factors are controlled on the fixed
positive radial interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff BigOperators Topology

theorem n06NuFiniteJetMap_spatial_composition_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (u v : E → N06NuJetCoordinates) (x : E) (δ : ℝ),
      ContDiffAt ℝ ∞ u x → ContDiffAt ℝ ∞ v x → 0 ≤ δ →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k v x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ ≤ δ) →
      (∀ w ∈ segment ℝ (v x) (u x), (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant w) →
      ‖iteratedFDeriv ℝ n (n06NuFiniteJetMap ∘ u) x -
        iteratedFDeriv ℝ n (n06NuFiniteJetMap ∘ v) x‖ ≤ Q * δ := by
  obtain ⟨C, hC, houter⟩ := n06NuFiniteJetMap_finite_derivative_bound M (n + 1)
  refine ⟨n06CompositionDifferenceCost n C M,
    n06CompositionDifferenceCost_nonneg n hC hM, ?_⟩
  intro u v x δ hu hv hδ hU hV hUV hdisc
  have hu₀ : ‖u x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hU 0 (Nat.zero_le n)
  have hv₀ : ‖v x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hV 0 (Nat.zero_le n)
  have hdiff₀ : ‖u x - v x‖ ≤ δ := by
    have he := iteratedFDeriv_sub_apply
      (hu.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
      (hv.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
    have h := hUV 0 (Nat.zero_le n)
    rw [← he, norm_iteratedFDeriv_zero] at h
    exact h
  have hvalue : ∀ w ∈ segment ℝ (v x) (u x), ‖w‖ ≤ M := by
    intro w hw
    have hvmem : v x ∈ Metric.closedBall (0 : N06NuJetCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv₀
    have humem : u x ∈ Metric.closedBall (0 : N06NuJetCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu₀
    have hwmem := (convex_closedBall (0 : N06NuJetCoordinates) M).segment_subset hvmem humem hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hwmem
  have hsmooth : ∀ w ∈ segment ℝ (v x) (u x), ContDiffAt ℝ ∞ n06NuFiniteJetMap w := by
    intro w hw
    exact n06NuFiniteJetMap_contDiffAt (lt_of_lt_of_le (by norm_num) (hdisc w hw))
  have hΦu := hsmooth (u x) (right_mem_segment ℝ (v x) (u x))
  have hΦv := hsmooth (v x) (left_mem_segment ℝ (v x) (u x))
  have houterValue (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06NuFiniteJetMap (u x)‖ ≤ C :=
    houter k (by omega) (u x) hu₀ (hdisc (u x) (right_mem_segment ℝ _ _))
  have houterDifference (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06NuFiniteJetMap (u x) -
        iteratedFDeriv ℝ k n06NuFiniteJetMap (v x)‖ ≤ C * δ := by
    have h := n06_iteratedFDeriv_difference_le_segment k hsmooth
      (fun w hw => houter (k + 1) (by omega) w (hvalue w hw) (hdisc w hw))
    exact h.trans (mul_le_mul_of_nonneg_left hdiff₀ hC)
  exact n06_iteratedFDeriv_comp_difference_le n hΦu hΦv hu hv hC hM hδ
    houterValue houterDifference hU hV hUV

/-- Coordinatewise bounds control the actual operator norm of a finite
vector-valued spatial derivative, with the product max norm. -/
theorem n06_norm_iteratedFDeriv_pi_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ i, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ R := by
  classical
  apply (iteratedFDeriv ℝ n f x).opNorm_le_bound hR
  intro v
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg hR (Finset.prod_nonneg fun _ _ => norm_nonneg _))).mpr
  intro i
  have he := congrArg (fun A => A v)
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left hf
      (i := n) (by simp))
  change iteratedFDeriv ℝ n (fun y => f y i) x v =
    (iteratedFDeriv ℝ n f x v) i at he
  rw [← he]
  exact ((iteratedFDeriv ℝ n (fun y => f y i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h i) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

/-- Taking a fixed physical directional derivative costs one spatial
derivative. The statement is local on the original open set. -/
theorem n06_norm_iteratedFDeriv_directional_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (d : PolarPoint) (n : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ f q d) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f p‖ * ‖d‖ := by
  have hc : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  apply (iteratedFDeriv ℝ n (fun q => fderiv ℝ f q d) p).opNorm_le_bound (by positivity)
  intro v
  have he := iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hc
    (i := n) (by simp) hp (u := d) (m := v)
  rw [iteratedFDerivWithin_of_isOpen n hU hp,
    iteratedFDerivWithin_of_isOpen n hU hp] at he
  rw [he]
  calc
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) p v d‖ ≤
        ‖iteratedFDeriv ℝ n (fderiv ℝ f) p v‖ * ‖d‖ :=
      (iteratedFDeriv ℝ n (fderiv ℝ f) p v).le_opNorm d
    _ ≤ (‖iteratedFDeriv ℝ n (fderiv ℝ f) p‖ * ∏ i, ‖v i‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right ((iteratedFDeriv ℝ n (fderiv ℝ f) p).le_opNorm v)
        (norm_nonneg d)
    _ = (‖iteratedFDeriv ℝ (n + 1) f p‖ * ‖d‖) * ∏ i, ‖v i‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      ring

theorem n06_norm_iteratedFDeriv_mul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f g : E → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) {x : E} (hx : x ∈ U) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hG : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ n * A * B := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  refine h.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hF i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hG (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ n * A * B := by
      have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, ← Finset.sum_mul, hs]

theorem n06_radialLift_frechet_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p.1 ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q : PolarPoint => f q.1) p‖ ≤
      ‖iteratedFDeriv ℝ n f p.1‖ := by
  let P : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hpre : IsOpen (P ⁻¹' U) := hU.preimage P.continuous
  have he := P.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn
    (x := p) hp (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp] at he
  change iteratedFDeriv ℝ n (fun q : PolarPoint => f q.1) p =
    (iteratedFDerivWithin ℝ n f U p.1).compContinuousLinearMap (fun _ => P) at he
  rw [iteratedFDerivWithin_of_isOpen n hU hp] at he
  rw [he]
  apply ((iteratedFDeriv ℝ n f p.1).compContinuousLinearMap
    (fun _ : Fin n => P)).opNorm_le_bound (norm_nonneg _)
  intro v
  change ‖iteratedFDeriv ℝ n f p.1 (fun i => (v i).1)‖ ≤
    ‖iteratedFDeriv ℝ n f p.1‖ * ∏ i, ‖v i‖
  exact ((iteratedFDeriv ℝ n f p.1).le_opNorm (fun i => (v i).1)).trans
    (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => norm_fst_le (v i))) (norm_nonneg _))

/-- A fixed smooth radial field has all its physical spatial derivatives
uniformly bounded over the positive compact radial interval, at every angle. -/
theorem n06_radialLift_finite_frechet_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} (ha : 0 < a)
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, k ≤ n → ∀ p : PolarPoint,
      p.1 ∈ Icc a b → ‖iteratedFDeriv ℝ k (fun q : PolarPoint => f q.1) p‖ ≤ B := by
  classical
  have hchoices (i : Fin (n + 1)) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ r ∈ Icc a b, ‖iteratedFDeriv ℝ i.val f r‖ ≤ B := by
    have hc : ContinuousOn (fun r => ‖iteratedFDeriv ℝ i.val f r‖) (Icc a b) := by
      intro r hr
      exact ((hf.contDiffAt (isOpen_Ioi.mem_nhds (ha.trans_le hr.1))).continuousAt_iteratedFDeriv
        (by simp)).norm.continuousWithinAt
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hc
    exact ⟨max B 0, le_max_right _ _, fun r hr =>
      (hB ⟨r, hr, rfl⟩).trans (le_max_left _ _)⟩
  choose c hc hbound using hchoices
  refine ⟨∑ i : Fin (n + 1), c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro k hk p hp
  let i : Fin (n + 1) := ⟨k, by omega⟩
  exact (n06_radialLift_frechet_le isOpen_Ioi hf k (ha.trans_le hp.1)).trans
    ((hbound i p.1 hp).trans
      (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)))

end ContinuousFlexibility.Analysis
