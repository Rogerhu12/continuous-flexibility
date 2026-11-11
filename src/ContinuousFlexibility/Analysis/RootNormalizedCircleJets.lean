import ContinuousFlexibility.Analysis.CircleLiftCompositionJets
import ContinuousFlexibility.Analysis.RootInverseNormalizedBounds

/-!
# Actual angular normalization of the controlled root inverse

The inverse flow displacement and the angular normalization displacement
are composed before the root substitution. Their actual derivatives obey
one common fixed loss. Restricting the angular representative to one
period then supplies full ordinary root-input jets, including order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

/-- The input estimates concern the original two displacements. The
output concerns their actual composition at the normalized root argument;
no derivative estimate of that composite is assumed. -/
theorem rootNormalizedCircleComposition_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
      ∀ g : N04FlowPoint → ℝ, ContDiff ℝ ∞ g →
      (∀ (n : ℕ) (θ : ℝ), ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
      (∀ (n : ℕ) (q : N04FlowPoint), q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ n (fun y => g y - y.2) q‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
      ∀ τ : ℝ, |τ| ≤ 1 → ∀ s : ℕ,
        CSBound s rootInputBox (h ∘ (g ∘ rootFlowNormalizedArgument τ))
          (B s * (1 + p (s + loss) z)) := by
  obtain ⟨base, loss, hcomposition⟩ :=
    circleLiftComposition_displacement_fixed_loss (X := N04FlowPoint) hp hI inputLoss
  choose C hC hnormalized using exists_csBound_rootFlowNormalizedInverse
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨D, hD, hbound⟩ := hcomposition A hA
  let H : ℕ → ℝ := fun s => ∑ n ∈ Finset.range (s + 1), D n
  have hH (s : ℕ) : 0 ≤ H s := Finset.sum_nonneg (fun n _ => (hD n).le)
  have hDH (s n : ℕ) (hn : n ≤ s) : D n ≤ H s :=
    Finset.single_le_sum (f := D) (fun n _ => (hD n).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  let B : ℕ → ℝ := fun s => C s * (1 + H s)
  refine ⟨B, fun s => mul_pos (hC s) (by linarith [hH s]), ?_⟩
  intro z hz h hh g hg houter hinner τ hτ s
  let L : N04FlowPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  let M : ℝ := H s * (1 + p (s + loss) z)
  have hstate : 1 ≤ 1 + p (s + loss) z :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  have hM : 0 ≤ M := mul_nonneg (hH s) (zero_le_one.trans hstate)
  have hdisplacement : CSBound s (n04FlowParameterBox ×ˢ (univ : Set ℝ))
      (fun y => (h ∘ g) y - y.2) M := by
    intro n hn q hq
    have hb := hbound z hz h hh g hg L
      (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ) q
      (fun j => houter j (g q))
      (fun j => hinner j q hq.1) n
    have hb' : ‖iteratedFDeriv ℝ n (fun y => (h ∘ g) y - y.2) q‖ ≤
        D n * (1 + p (n + loss) z) := by
      simpa only [L, ContinuousLinearMap.coe_snd', Function.comp_apply] using hb
    exact hb'.trans (mul_le_mul (hDH s n hn)
      (add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_right hn loss)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hH s))
  have hb := hnormalized s (h ∘ g) (hh.comp hg) M hM hdisplacement τ hτ
  have he : (h ∘ g) ∘ rootFlowNormalizedArgument τ =
      h ∘ (g ∘ rootFlowNormalizedArgument τ) := rfl
  rw [he] at hb
  apply hb.mono_bound
  calc
    C s * (M + 1) ≤ C s * (M + (1 + p (s + loss) z)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hstate) (hC s).le
    _ = B s * (1 + p (s + loss) z) := by
      dsimp only [M, B]
      ring

end ContinuousFlexibility.Analysis
