import ContinuousFlexibility.Analysis.N06RelativeBoundaryPatch
import ContinuousFlexibility.Analysis.N06PositiveCutoffJets

/-!
# Quantitative jets of the actual relative Taylor correction

The radial factors are the fixed bump times the actual Taylor monomials.
Their rescaling has an explicit inverse-width cost. Consequently every
finite spatial jet of the existing boundary extension is bounded linearly
by the angular jets of its actual boundary data. The constant is uniform
in the endpoints and in the collar width; the width dependence is displayed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

private def n06TaylorKernel (j : ℕ) (t : ℝ) : ℝ :=
  boundaryTaylorCutoff t * (t ^ j / (j.factorial : ℝ))

private theorem n06TaylorKernel_smooth (j : ℕ) :
    ContDiff ℝ ∞ (n06TaylorKernel j) :=
  boundaryTaylorCutoff.contDiff.mul ((contDiff_id.pow j).div_const _)

private theorem n06TaylorKernel_jet_bounded (j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k (n06TaylorKernel j) t| ≤ C := by
  have hs : HasCompactSupport (n06TaylorKernel j) :=
    boundaryTaylorCutoff.hasCompactSupport.mul_right
  have hsk : HasCompactSupport (iteratedDeriv k (n06TaylorKernel j)) := by
    induction k with
    | zero => exact hs
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  obtain ⟨C, hC⟩ := hsk.exists_bound_of_continuous
    ((n06TaylorKernel_smooth j).continuous_iteratedDeriv k (by simp))
  refine ⟨max 0 C, le_max_left _ _, fun t => ?_⟩
  exact (show |iteratedDeriv k (n06TaylorKernel j) t| ≤ C by
    simpa only [Real.norm_eq_abs] using hC t).trans (le_max_right _ _)

private theorem n06TaylorKernel_scale {δ : ℝ} (hδ : 0 < δ) (j : ℕ) (c x : ℝ) :
    positiveEndpointCutoff c δ x * ((x - c) ^ j / (j.factorial : ℝ)) =
      δ ^ j * n06TaylorKernel j ((x - c) / δ) := by
  have he : (x - c) ^ j = δ ^ j * ((x - c) / δ) ^ j := by
    rw [← mul_pow]
    congr 1
    field_simp
  simp only [positiveEndpointCutoff, n06TaylorKernel]
  rw [he]
  ring

private theorem n06TaylorKernel_scaled_derivative {δ : ℝ} (hδ : 0 < δ)
    (j k : ℕ) (c x : ℝ) :
    iteratedDeriv k
        (fun t => positiveEndpointCutoff c δ t * ((t - c) ^ j / (j.factorial : ℝ))) x =
      δ ^ j * (δ⁻¹ ^ k * iteratedDeriv k (n06TaylorKernel j) ((x - c) / δ)) := by
  have he : (fun t => positiveEndpointCutoff c δ t * ((t - c) ^ j / (j.factorial : ℝ))) =
      fun t => δ ^ j * n06TaylorKernel j (δ⁻¹ * (t - c)) := by
    funext t
    simpa only [div_eq_mul_inv, mul_comm δ⁻¹] using n06TaylorKernel_scale hδ j c t
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_sub_const k (fun t => n06TaylorKernel j (δ⁻¹ * t)) c,
    iteratedDeriv_comp_const_mul ((n06TaylorKernel_smooth j).of_le (by simp))]
  simp only [div_eq_mul_inv, mul_comm δ⁻¹]

/-- All the actual radial Taylor factors have one finite-jet bound. -/
theorem n06_boundaryTaylor_radial_factor_bound (n m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j, j ≤ n → ∀ k, k ≤ m → ∀ c δ x : ℝ,
      0 < δ → δ ≤ 1 →
      |iteratedDeriv k
        (fun t => positiveEndpointCutoff c δ t * ((t - c) ^ j / (j.factorial : ℝ))) x| ≤
          C * δ⁻¹ ^ m := by
  classical
  let I := Fin (n + 1) × Fin (m + 1)
  have hc (i : I) := n06TaylorKernel_jet_bounded i.1.val i.2.val
  choose c hc hb using hc
  let C : ℝ := 1 + ∑ i : I, c i
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hc i))
  refine ⟨C, hC, ?_⟩
  intro j hj k hk a δ x hδ hδ1
  let i : I := (⟨j, by omega⟩, ⟨k, by omega⟩)
  have hi : c i ≤ C :=
    (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hkC : |iteratedDeriv k (n06TaylorKernel j) ((x - a) / δ)| ≤ C :=
    (hb i _).trans hi
  have hpow : δ ^ j ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hi0 : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hipow : δ⁻¹ ^ k ≤ δ⁻¹ ^ m :=
    pow_le_pow_right₀ ((one_le_inv₀ hδ).mpr hδ1) hk
  rw [n06TaylorKernel_scaled_derivative hδ, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg hδ.le j), abs_of_nonneg (pow_nonneg hi0 k)]
  calc
    _ ≤ 1 * (δ⁻¹ ^ m * C) := mul_le_mul hpow
      (mul_le_mul hipow hkC (abs_nonneg _) (pow_nonneg hi0 m))
      (mul_nonneg (pow_nonneg hi0 k) (abs_nonneg _)) zero_le_one
    _ = C * δ⁻¹ ^ m := by ring

private theorem n06_separated_mixedDerivative (f g : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q.1 * g q.2) p =
      iteratedDeriv a f p.1 * iteratedDeriv b g p.2 := by
  simp only [mixedDerivative, iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]

private theorem n06TaylorTerm_frechet_bound {n m : ℕ} {C M c δ : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hr : ∀ j, j ≤ n → ∀ k, k ≤ m → ∀ x,
      |iteratedDeriv k
        (fun t => positiveEndpointCutoff c δ t * ((t - c) ^ j / (j.factorial : ℝ))) x| ≤
          C * δ⁻¹ ^ m)
    {a : ℕ → ℝ → ℝ} (ha : ∀ j ≤ n, ContDiff ℝ ∞ (a j))
    (hb : ∀ j ≤ n, ∀ k ≤ m, ∀ θ, |iteratedDeriv k (a j) θ| ≤ M)
    {j k : ℕ} (hj : j ≤ n) (hk : k ≤ m) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ k
      (fun q : PolarPoint =>
        (positiveEndpointCutoff c δ q.1 * ((q.1 - c) ^ j / (j.factorial : ℝ))) * a j q.2) p‖ ≤
      ((2 : ℝ) ^ m * C * δ⁻¹ ^ m) * M := by
  let f : ℝ → ℝ := fun t => positiveEndpointCutoff c δ t * ((t - c) ^ j / (j.factorial : ℝ))
  have hf : ContDiff ℝ ∞ f := (contDiff_positiveEndpointCutoff c δ).mul
    (((contDiff_id.sub contDiff_const).pow j).div_const _)
  have hs : ContDiff ℝ ∞ (fun q : PolarPoint => f q.1 * a j q.2) :=
    (hf.comp contDiff_fst).mul ((ha j hj).comp contDiff_snd)
  have hcost : 0 ≤ C * δ⁻¹ ^ m * M := by positivity
  have h := norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ hs.contDiffOn k
    (Set.mem_univ p) hcost (fun r s hrs => by
      rw [n06_separated_mixedDerivative, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hr j hj r (by omega) p.1) (hb j hj s (by omega) p.2)
        (abs_nonneg _) (by positivity))
  exact h.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hcost).trans_eq (by ring))

/-- One endpoint's existing cutoff polynomial has all finite spatial
jets bounded linearly in its angular boundary jets. -/
theorem n06_boundaryTaylor_endpoint_frechet_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c δ M : ℝ) (a : ℕ → ℝ → ℝ),
      0 < δ → δ ≤ 1 → 0 ≤ M →
      (∀ j ≤ n, ContDiff ℝ ∞ (a j)) →
      (∀ j ≤ n, ∀ k ≤ m, ∀ θ, |iteratedDeriv k (a j) θ| ≤ M) →
      ∀ k, k ≤ m → ∀ p : PolarPoint,
      ‖iteratedFDeriv ℝ k
        (fun q => positiveEndpointCutoff c δ q.1 * boundaryTaylorPolynomial n c a q) p‖ ≤
          C * δ⁻¹ ^ m * M := by
  obtain ⟨A, hA, hr⟩ := n06_boundaryTaylor_radial_factor_bound n m
  refine ⟨((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ m * A, by positivity, ?_⟩
  intro c δ M a hδ hδ1 hM ha hb k hk p
  let F : ℕ → PolarPoint → ℝ := fun j q =>
    (positiveEndpointCutoff c δ q.1 * ((q.1 - c) ^ j / (j.factorial : ℝ))) * a j q.2
  have hF (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : ContDiff ℝ ∞ (F j) :=
    (((contDiff_positiveEndpointCutoff c δ).comp contDiff_fst).mul
      (((contDiff_fst.sub contDiff_const).pow j).div_const _)).mul
        ((ha j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).comp contDiff_snd)
  have he : (fun q => positiveEndpointCutoff c δ q.1 * boundaryTaylorPolynomial n c a q) =
      fun q => ∑ j ∈ Finset.range (n + 1), F j q := by
    funext q
    simp only [boundaryTaylorPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [F]
    ring
  rw [he, iteratedFDeriv_fun_sum_apply (fun j hj =>
    ((hF j hj).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (F j) p‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (n + 1), ((2 : ℝ) ^ m * A * δ⁻¹ ^ m) * M := by
      apply Finset.sum_le_sum
      intro j hj
      exact n06TaylorTerm_frechet_bound (zero_le_one.trans hA) hM hδ
        (fun j hj k hk x => hr j hj k hk c δ x hδ hδ1) ha hb
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hk p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Both endpoints are controlled by the same constant and the same
radius. This is the actual correction already used in the relative patch. -/
theorem n06SmallBoundaryExtension_frechet_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l r δ M : ℝ) (a b : ℕ → ℝ → ℝ),
      0 < δ → δ ≤ 1 → 0 ≤ M →
      (∀ j ≤ n, ContDiff ℝ ∞ (a j)) →
      (∀ j ≤ n, ContDiff ℝ ∞ (b j)) →
      (∀ j ≤ n, ∀ k ≤ m, ∀ θ, |iteratedDeriv k (a j) θ| ≤ M) →
      (∀ j ≤ n, ∀ k ≤ m, ∀ θ, |iteratedDeriv k (b j) θ| ≤ M) →
      ∀ k, k ≤ m → ∀ p : PolarPoint,
      ‖iteratedFDeriv ℝ k (n06SmallBoundaryExtension n l r δ a b) p‖ ≤
        C * δ⁻¹ ^ m * M := by
  obtain ⟨A, hA, hb⟩ := n06_boundaryTaylor_endpoint_frechet_bound n m
  refine ⟨2 * A, by positivity, ?_⟩
  intro l r δ M a b hδ hδ1 hM ha hb' hba hbb k hk p
  have hL : ContDiff ℝ ∞
      (fun q => positiveEndpointCutoff l δ q.1 * boundaryTaylorPolynomial n l a q) :=
    ((contDiff_positiveEndpointCutoff l δ).comp contDiff_fst).mul
      (contDiff_boundaryTaylorPolynomial ha l)
  have hR : ContDiff ℝ ∞
      (fun q => positiveEndpointCutoff r δ q.1 * boundaryTaylorPolynomial n r b q) :=
    ((contDiff_positiveEndpointCutoff r δ).comp contDiff_fst).mul
      (contDiff_boundaryTaylorPolynomial hb' r)
  unfold n06SmallBoundaryExtension
  have he := iteratedFDeriv_add_apply (x := p)
    ((hL.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
    ((hR.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
  simp only [Pi.add_def] at he
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add
    (hb l δ M a hδ hδ1 hM ha hba k hk p)
    (hb r δ M b hδ hδ1 hM hb' hbb k hk p))).trans_eq (by ring)

/-- Applied to the actual target-minus-reference data, the bound is
linear in precisely those differences. Reference smoothness is needed
only on the two boundary axes. -/
theorem n06RelativeBoundaryPatch_difference_frechet_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l r δ M : ℝ)
      (f₀ : PolarPoint → ℝ) (f : Bool → PolarPoint → ℝ),
      0 < δ → δ ≤ 1 → 0 ≤ M →
      (∀ (side : Bool) θ, ContDiffAt ℝ ∞ f₀ (if side then r else l, θ)) →
      (∀ (side : Bool) θ, ContDiffAt ℝ ∞ (f side) (if side then r else l, θ)) →
      (∀ side j, j ≤ n → ∀ k, k ≤ m → ∀ θ,
        |iteratedDeriv k
          (radialBoundaryJet (fun p => f side p - f₀ p) (if side then r else l) j) θ| ≤ M) →
      ∀ k, k ≤ m → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k (fun q => n06RelativeBoundaryPatch n l r δ f₀ f q - f₀ q) p‖ ≤
          C * δ⁻¹ ^ m * M := by
  obtain ⟨C, hC, hb⟩ := n06SmallBoundaryExtension_frechet_bound n m
  refine ⟨C, hC, ?_⟩
  intro l r δ M f₀ f hδ hδ1 hM h₀ hf hdata k hk p
  have he : (fun q => n06RelativeBoundaryPatch n l r δ f₀ f q - f₀ q) =
      n06SmallBoundaryExtension n l r δ
        (radialBoundaryJet (fun q => f false q - f₀ q) l)
        (radialBoundaryJet (fun q => f true q - f₀ q) r) := by
    funext q
    simp only [n06RelativeBoundaryPatch, add_sub_cancel_left]
  rw [he]
  exact hb l r δ M _ _ hδ hδ1 hM
    (fun j _ => n06_contDiff_radialBoundaryJet_of_axis
      (fun θ => (hf false θ).sub (h₀ false θ)) j)
    (fun j _ => n06_contDiff_radialBoundaryJet_of_axis
      (fun θ => (hf true θ).sub (h₀ true θ)) j)
    (hdata false) (hdata true) k hk p

end ContinuousFlexibility.Analysis
