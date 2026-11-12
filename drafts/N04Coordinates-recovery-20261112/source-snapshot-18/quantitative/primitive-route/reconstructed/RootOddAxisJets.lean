import ContinuousFlexibility.Analysis.RootEvenAxisJets
import ContinuousFlexibility.Analysis.RootOddBounds

/-!
# Genuine odd root jets with one input derivative

The odd divided difference is the actual integral of a middle derivative.
At the root every integration sample is the same original source point.
The fixed polynomial integrand map has angular-translation-invariant
positive jets, so a fixed compact estimate for that map has no component,
angle, model-radius or normalization-scale cost.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology Interval BigOperators

private def rootOddAxisKernel : (ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ × ℝ :=
  fun q => (q.1.1, q.2 * q.1.2.1, q.1.2.2)

private theorem rootOddAxisKernel_contDiff : ContDiff ℝ ∞ rootOddAxisKernel :=
  contDiff_fst.fst.prodMk
    ((contDiff_snd.mul contDiff_fst.snd.fst).prodMk contDiff_fst.snd.snd)

private theorem rootOddAxisKernel_positive_jet_shift (i : ℕ) (hi : 1 ≤ i) (θ t : ℝ) :
    iteratedFDeriv ℝ i rootOddAxisKernel ((0, 0, θ), t) =
      iteratedFDeriv ℝ i rootOddAxisKernel ((0, 0, 0), t) := by
  let v : (ℝ × ℝ × ℝ) × ℝ := ((0, 0, θ), 0)
  have hp : (((0, 0, 0), t) : (ℝ × ℝ × ℝ) × ℝ) + v = ((0, 0, θ), t) := by
    ext <;> simp [v]
  have he : (fun y => rootOddAxisKernel (y + v)) =
      rootOddAxisKernel + (fun _ => (0, 0, θ)) := by
    funext y
    simp only [rootOddAxisKernel, v, Prod.add_def, Pi.add_apply, add_zero, zero_add,
      mul_zero, zero_mul]
  calc
    _ = iteratedFDeriv ℝ i (fun y => rootOddAxisKernel (y + v)) ((0, 0, 0), t) := by
      rw [iteratedFDeriv_comp_add_right, hp]
    _ = _ := by
      rw [he, iteratedFDeriv_add_apply
        (rootOddAxisKernel_contDiff.contDiffAt.of_le (by simp : (i : ℕ∞ω) ≤ ∞))
        (contDiffAt_const.of_le (by simp : (i : ℕ∞ω) ≤ ∞))]
      simp only [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hi), Pi.zero_apply, add_zero]

private theorem rootOddAxisKernel_jet_bound (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∀ θ t : ℝ, t ∈ Icc (-1 : ℝ) 1 →
      ‖iteratedFDeriv ℝ i rootOddAxisKernel ((0, 0, θ), t)‖ ≤ D ^ i := by
  let J : ℝ → ℝ := fun t =>
    ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i rootOddAxisKernel ((0, 0, 0), t)‖
  have hJ : Continuous J := continuous_finsetSum _ (fun i _ =>
    ((rootOddAxisKernel_contDiff.continuous_iteratedFDeriv (by simp)).norm).comp
      (continuous_const.prodMk continuous_id))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hJ.continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro i hi hin θ t ht
  rw [rootOddAxisKernel_positive_jet_shift i hi θ t]
  have hJnonneg : 0 ≤ J t := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hb := hB t ht
  rw [Real.norm_of_nonneg hJnonneg] at hb
  have hiJ : ‖iteratedFDeriv ℝ i rootOddAxisKernel ((0, 0, 0), t)‖ ≤ J t :=
    Finset.single_le_sum (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
  exact (hiJ.trans hb).trans ((le_max_right 1 B).trans
    (le_self_pow₀ (le_max_left 1 B) (Nat.ne_of_gt hi)))

/-- The actual odd integral at the root loses only one source derivative.
Its coefficient is fixed before the input and the root angle. -/
theorem exists_rootOddIntegral_axis_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ θ M : ℝ, (∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k G (0, 0, θ)‖ ≤ M) →
      ‖iteratedFDeriv ℝ n (rootOddIntegral G) (0, 0, θ)‖ ≤ C * M := by
  obtain ⟨D, hD, hkernel⟩ := rootOddAxisKernel_jet_bound n
  let C : ℝ := (n.factorial : ℝ) * D ^ n
  have hC : 0 < C := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    (pow_pos (zero_lt_one.trans_le hD) n)
  refine ⟨C, hC, ?_⟩
  intro G hG θ M hB
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) )
  have hmiddle := contDiff_rootMiddleDerivative hG
  have hmiddleBound (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (rootMiddleDerivative G) (0, 0, θ)‖ ≤ M := by
    have hv : ‖((0, 1, 0) : ℝ × ℝ × ℝ)‖ = 1 := by norm_num [Prod.norm_mk]
    have hh := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ G) (c := ((0, 1, 0) : ℝ × ℝ × ℝ)) (x := (0, 0, θ)) (n := i)
      (contDiff_infty_iff_fderiv.mp hG).2.contDiffAt (by simp)
    have hnext : ‖iteratedFDeriv ℝ i (rootMiddleDerivative G) (0, 0, θ)‖ ≤
        ‖iteratedFDeriv ℝ (i + 1) G (0, 0, θ)‖ := by
      unfold rootMiddleDerivative
      simpa only [hv, one_mul, norm_iteratedFDeriv_fderiv] using hh
    exact hnext.trans (hB (i + 1) (Nat.add_le_add_right hi 1))
  have hIntegrand : ContDiff ℝ ∞ (rootMiddleDerivative G ∘ rootOddAxisKernel) :=
    hmiddle.comp rootOddAxisKernel_contDiff
  have hIntegral : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ =>
      ∫ t in (-1 : ℝ)..1, (rootMiddleDerivative G ∘ rootOddAxisKernel) (q, t)) :=
    contDiff_intervalIntegral_of_contDiff hIntegrand (-1) 1
  have hbound : ∀ t ∈ uIcc (-1 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (rootMiddleDerivative G ∘ rootOddAxisKernel) ((0, 0, θ), t)‖ ≤
        C * M := by
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have hpoint : rootOddAxisKernel ((0, 0, θ), t) = (0, 0, θ) := by
      simp only [rootOddAxisKernel, mul_zero]
    have hc := norm_iteratedFDeriv_comp_le hmiddle rootOddAxisKernel_contDiff
      (by simp) ((0, 0, θ), t) (C := M) (D := D)
      (fun i hi => by rw [hpoint]; exact hmiddleBound i hi)
      (fun i hi hin => hkernel i hi hin θ t ht')
    exact hc.trans_eq (by dsimp only [C]; ring)
  have hb := norm_iteratedFDeriv_intervalIntegral_le hIntegrand n (-1) 1 (0, 0, θ)
    (C * M) hbound
  norm_num at hb
  have hscale : iteratedFDeriv ℝ n (rootOddIntegral G) (0, 0, θ) =
      (1 / 2 : ℝ) • iteratedFDeriv ℝ n
        (fun q : ℝ × ℝ × ℝ => ∫ t in (-1 : ℝ)..1,
          (rootMiddleDerivative G ∘ rootOddAxisKernel) (q, t)) (0, 0, θ) := by
    unfold rootOddIntegral
    simpa only [Function.comp_def, rootOddAxisKernel, smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := (1 / 2 : ℝ))
        (hIntegral.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)))
  rw [hscale, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)

/-- The same one-derivative loss holds for the genuine smooth extension
of the negative odd coefficient, rather than the raw totalized quotient. -/
theorem exists_rootOddCoefficient_axis_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ F : PolarPoint → ℝ, ContDiff ℝ ∞ F →
      EqOn F (fun p => -rootOdd G p) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) →
      ∀ θ M : ℝ, (∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k G (0, 0, θ)‖ ≤ M) →
      ‖iteratedFDeriv ℝ n F (0, θ)‖ ≤ C * M := by
  classical
  obtain ⟨CE, hCE, heven⟩ := exists_rootEven_axis_jet_bound n
  choose CI hCI hintegral using exists_rootOddIntegral_axis_jet_bound
  let A : ℝ := ∑ k ∈ Finset.range (n + 1), CI k
  have hA : 0 < A := Finset.sum_pos (fun k _ => hCI k)
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
  refine ⟨CE * A, mul_pos hCE hA, ?_⟩
  intro G hG F hF hEq θ M hB
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hinput (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k (rootOddIntegral G) (0, 0, θ)‖ ≤ A * M := by
    have hCA : CI k ≤ A := Finset.single_le_sum (fun k _ => (hCI k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact (hintegral k G hG θ M (fun j hj =>
      hB j (hj.trans (Nat.add_le_add_right hk 1)))).trans
      (mul_le_mul_of_nonneg_right hCA hM)
  have heq : EqOn (-F) (rootEven (rootOddIntegral G))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    rw [Pi.neg_apply, hEq hp, neg_neg]
    exact (rootEven_rootOddIntegral_eqOn hG ⟨hp.1.le, mem_univ _⟩).symm
  have hb := heven (rootOddIntegral G) (contDiff_rootOddIntegral hG)
    (-F) hF.neg heq θ (A * M) hinput
  simpa only [iteratedFDeriv_neg_apply, norm_neg, mul_assoc] using hb

end ContinuousFlexibility.Analysis
