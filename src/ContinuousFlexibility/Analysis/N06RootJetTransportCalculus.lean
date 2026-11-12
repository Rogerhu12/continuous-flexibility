import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
import ContinuousFlexibility.Analysis.N06RootPhysicalWeightedSmallness
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Jet transport used by the actual factored root fields

The physical root shift is a translation and, at the right endpoint, a
radial reflection. It therefore preserves every full derivative norm.
The remaining cost for the actual factored characteristic speed is the
finite jet cost of its fixed radial reference factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

private def n06RootRadialReflection : PolarPoint ≃ₗᵢ[ℝ] PolarPoint where
  toLinearEquiv := (LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ).prodCongr (LinearEquiv.refl ℝ ℝ)
  norm_map' p := by
    change max ‖-p.1‖ ‖p.2‖ = max ‖p.1‖ ‖p.2‖
    rw [norm_neg]

theorem n06_rootProfileShift_contDiff (r σ : ℝ) :
    ContDiff ℝ ∞ (rootProfileShift r σ) :=
  (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd

/-- Reorientation of the physical root does not enlarge any spatial jet.
This equality requires no regularity of the function. -/
theorem n06_norm_iteratedFDeriv_rootProfileShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : PolarPoint → E) (r σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (n : ℕ) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ n (f ∘ rootProfileShift r σ) p‖ =
      ‖iteratedFDeriv ℝ n f (rootProfileShift r σ p)‖ := by
  rcases hσ with rfl | rfl
  · have he : f ∘ rootProfileShift r 1 = fun q => f (q + (r, 0)) := by
      funext q
      change f (rootProfileShift r 1 q) = f (q + (r, 0))
      congr 1
      apply Prod.ext
      · simp only [rootProfileShift, Prod.fst_add, one_mul, add_comm]
      · simp only [rootProfileShift, Prod.snd_add, add_zero]
    rw [he, iteratedFDeriv_comp_add_right]
    have hp : p + (r, 0) = rootProfileShift r 1 p := by
      apply Prod.ext
      · simp only [rootProfileShift, Prod.fst_add, one_mul, add_comm]
      · simp only [rootProfileShift, Prod.snd_add, add_zero]
    rw [hp]
  · let g : PolarPoint → E := fun q => f (q + (r, 0))
    have he : f ∘ rootProfileShift r (-1) = g ∘ n06RootRadialReflection := by
      funext q
      change f (r + -1 * q.1, q.2) = f (-q.1 + r, q.2 + 0)
      congr 1 <;> simp only [neg_one_mul, add_zero, add_comm]
    rw [he, n06RootRadialReflection.norm_iteratedFDeriv_comp_right]
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_right]
    have hp : n06RootRadialReflection p + (r, 0) = rootProfileShift r (-1) p := by
      change (-p.1 + r, p.2 + 0) = (r + -1 * p.1, p.2)
      simp only [neg_one_mul, add_zero, add_comm]
    rw [hp]

theorem n06_norm_iteratedFDeriv_fst_le
    {f : PolarPoint → PolarPoint} {p : PolarPoint}
    (hf : ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => (f q).1) p‖ ≤ ‖iteratedFDeriv ℝ n f p‖ := by
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one
    (fun q : PolarPoint => by
      change ‖q.1‖ ≤ 1 * ‖q‖
      simpa only [one_mul] using norm_fst_le q)
  exact (L.norm_iteratedFDeriv_comp_left hf (n := n) (by simp)).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

theorem n06_norm_iteratedFDeriv_snd_le
    {f : PolarPoint → PolarPoint} {p : PolarPoint}
    (hf : ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => (f q).2) p‖ ≤ ‖iteratedFDeriv ℝ n f p‖ := by
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one
    (fun q : PolarPoint => by
      change ‖q.2‖ ≤ 1 * ‖q‖
      simpa only [one_mul] using norm_snd_le q)
  exact (L.norm_iteratedFDeriv_comp_left hf (n := n) (by simp)).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

theorem n06_norm_iteratedFDeriv_real_mul_at {f : PolarPoint → ℝ} {p : PolarPoint}
    (hf : ContDiffAt ℝ ∞ f p) (q : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => q * f x) p‖ = |q| * ‖iteratedFDeriv ℝ n f p‖ := by
  have h := iteratedFDeriv_const_smul_apply' (a := q) (x := p)
    (hf.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
  exact (congrArg norm h).trans (norm_smul q _)

/-- A finite product estimate using only smoothness at the actual point. -/
theorem n06_norm_iteratedFDeriv_mul_at_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (n : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hG : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ n * A * B := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn'
    (by simp : (n : ℕ∞ω) ≤ ∞) (by simp)
  obtain ⟨V, hV, hxV, hgV⟩ := hg.contDiffOn'
    (by simp : (n : ℕ∞ω) ≤ ∞) (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hfU hgV
  have hW : IsOpen (U ∩ V) := hU.inter hV
  have hx : x ∈ U ∩ V := ⟨hxU, hxV⟩
  have h := norm_iteratedFDerivWithin_mul_le
    (hfU.mono inter_subset_left) (hgV.mono inter_subset_right) hW.uniqueDiffOn hx
    (n := n) le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hW hx] at h
  refine h.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hF i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hG (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ n * A * B := by
      have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, ← Finset.sum_mul, hs]

/-- The reference cost consists of actual derivatives of the fixed
radial factor. It does not contain current-state data. -/
def n06RootRadialFactorJetCost (a : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), ‖iteratedFDeriv ℝ k.val (fun p : PolarPoint => a p.1) (0, 0)‖

theorem n06RootRadialFactorJetCost_nonneg (a : ℝ → ℝ) (n : ℕ) :
    0 ≤ n06RootRadialFactorJetCost a n :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem n06_radialFactor_jet_bound (a : ℝ → ℝ) (n k : ℕ) (hk : k ≤ n) (θ : ℝ) :
    ‖iteratedFDeriv ℝ k (fun p : PolarPoint => a p.1) (0, θ)‖ ≤
      n06RootRadialFactorJetCost a n := by
  classical
  have he := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun p : PolarPoint => a p.1) k ((0, θ) : PolarPoint) ((0, 0) : PolarPoint)
  have hfun : (fun p : PolarPoint => a (p + (0, θ)).1) = fun p => a p.1 := by
    funext p
    simp only [Prod.fst_add, add_zero]
  rw [hfun] at he
  have he' : iteratedFDeriv ℝ k (fun p : PolarPoint => a p.1) (0, 0) =
      iteratedFDeriv ℝ k (fun p : PolarPoint => a p.1) (0, θ) := by
    simpa only [Prod.mk_add_mk, zero_add] using he
  rw [← he']
  let i : Fin (n + 1) := ⟨k, by omega⟩
  exact Finset.single_le_sum (fun j _ => norm_nonneg
    (iteratedFDeriv ℝ j.val (fun p : PolarPoint => a p.1) (0, 0))) (Finset.mem_univ i)

end ContinuousFlexibility.Analysis
