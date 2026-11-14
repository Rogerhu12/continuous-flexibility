module

public import ContinuousFlexibility.Analysis.N04FlowInverseStateJets
public import ContinuousFlexibility.Analysis.RootCompositionBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Ordinary jets of the actual inverse on the root input rectangle

The root substitutions use the order `(r, ζ, θ)`.  Rescaling the second
parameter by a number of absolute value at most one is a linear contraction.
The angle itself is bounded on the chosen angular period; positive angle
jets are controlled by the projection norm.  Thus the actual inverse
displacement estimates give the complete ordinary input jets needed by
the even and odd root substitutions, with the same fixed state loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def rootFlowNormalizedArgument (σ : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] N04FlowPoint :=
  ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((σ • ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

theorem rootFlowNormalizedArgument_apply (σ : ℝ) (q : ℝ × ℝ × ℝ) :
    rootFlowNormalizedArgument σ q = ((q.1, σ * q.2.1), q.2.2) := by
  simp only [rootFlowNormalizedArgument, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem rootFlowNormalizedArgument_norm {σ : ℝ} (hσ : |σ| ≤ 1) :
    ‖rootFlowNormalizedArgument σ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [rootFlowNormalizedArgument_apply, one_mul, Prod.norm_def, Prod.norm_def,
    max_le_iff, max_le_iff]
  refine ⟨⟨norm_fst_le q, ?_⟩, (norm_snd_le q.2).trans (norm_snd_le q)⟩
  rw [norm_mul]
  have hσ' : ‖σ‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hσ
  exact (mul_le_mul_of_nonneg_right hσ' (norm_nonneg _)).trans
    (by simpa only [one_mul] using (norm_fst_le q.2).trans (norm_snd_le q))

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

private theorem rootFlowNormalizedArgument_mem {σ : ℝ} (hσ : |σ| ≤ 1)
    {q : ℝ × ℝ × ℝ} (hq : q ∈ rootInputBox) :
    (rootFlowNormalizedArgument σ q).1 ∈ n04FlowParameterBox := by
  rw [rootFlowNormalizedArgument_apply]
  refine ⟨⟨(by linarith [hq.1.1]), hq.1.2⟩, ?_⟩
  apply abs_le.mp
  rw [abs_mul]
  exact (mul_le_mul hσ (abs_le.mpr hq.2.1) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

private theorem scalarFamily_jet_le_displacement_on_period
    {g : N04FlowPoint → ℝ} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) {q : N04FlowPoint} (hq : q.2 ∈ Icc (-Real.pi) Real.pi)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => g y - y.2) q‖ ≤ M) :
    ‖iteratedFDeriv ℝ n g q‖ ≤ (2 + Real.pi) * (M + 1) := by
  have hproj : ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => y.2) q‖ ≤
      1 + Real.pi := by
    cases n with
    | zero =>
        simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact (abs_le.mpr hq).trans (by linarith)
    | succ n =>
        have hh := (flowJet_norm_iteratedFDeriv_clm_le
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (Nat.succ_pos n) q).trans
            (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ)
        have hscalar : ‖iteratedFDeriv ℝ (n + 1)
            (fun y : N04FlowPoint => y.2) q‖ ≤ 1 := by
          simpa only [ContinuousLinearMap.coe_snd'] using hh
        exact hscalar.trans (by linarith [Real.pi_pos])
  have he : g = (fun y : N04FlowPoint => g y - y.2) +
      (fun y : N04FlowPoint => y.2) := by
    funext y
    simp only [Pi.add_apply]
    exact (sub_add_cancel (g y) y.2).symm
  have hjet : iteratedFDeriv ℝ n g q =
      iteratedFDeriv ℝ n (fun y : N04FlowPoint => g y - y.2) q +
        iteratedFDeriv ℝ n (fun y : N04FlowPoint => y.2) q := by
    conv_lhs => rw [he]
    exact iteratedFDeriv_add_apply
      ((hg.sub contDiff_snd).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      contDiffAt_snd
  rw [hjet]
  apply (norm_add_le _ _).trans
  apply (add_le_add hbound hproj).trans
  nlinarith [Real.pi_pos]

/-- A finite displacement bound on the actual parameter box gives a
full finite ordinary bound after the normalized root argument. -/
theorem exists_csBound_rootFlowNormalizedInverse (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : N04FlowPoint → ℝ, ContDiff ℝ ∞ g →
      ∀ M : ℝ, 0 ≤ M →
      CSBound s (n04FlowParameterBox ×ˢ (univ : Set ℝ))
        (fun y : N04FlowPoint => g y - y.2) M →
      ∀ σ : ℝ, |σ| ≤ 1 →
        CSBound s rootInputBox (g ∘ rootFlowNormalizedArgument σ) (C * (M + 1)) := by
  let H : ℝ := 1 + ∑ k ∈ Finset.range (s + 1), (k.factorial : ℝ)
  have hH : 0 < H := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _))
  refine ⟨H * (2 + Real.pi), mul_pos hH (by linarith [Real.pi_pos]), ?_⟩
  intro g hg M hM hbound σ hσ n hn q hq
  have harg := rootFlowNormalizedArgument_mem hσ hq
  have hang : (rootFlowNormalizedArgument σ q).2 ∈ Icc (-Real.pi) Real.pi := by
    simpa only [rootFlowNormalizedArgument_apply] using hq.2.2
  have hraw (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k g (rootFlowNormalizedArgument σ q)‖ ≤
        (2 + Real.pi) * (M + 1) :=
    scalarFamily_jet_le_displacement_on_period hg k hang hM
      (hbound k (hk.trans hn) _ ⟨harg, mem_univ _⟩)
  have hcomp := norm_iteratedFDeriv_comp_le hg (rootFlowNormalizedArgument σ).contDiff
    (by simp : (n : ℕ∞ω) ≤ ∞) q (C := (2 + Real.pi) * (M + 1)) (D := (1 : ℝ))
    hraw (fun k hk _ => by
      simpa only [one_pow] using
        (flowJet_norm_iteratedFDeriv_clm_le (rootFlowNormalizedArgument σ) hk q).trans
          (rootFlowNormalizedArgument_norm hσ))
  have hfactor : (n.factorial : ℝ) ≤ H := by
    have hh := Finset.single_le_sum (f := fun k : ℕ => (k.factorial : ℝ))
      (fun k _ => Nat.cast_nonneg k.factorial)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact hh.trans (by dsimp only [H]; linarith)
  have hraw0 : 0 ≤ (2 + Real.pi) * (M + 1) :=
    mul_nonneg (by linarith [Real.pi_pos]) (by linarith)
  have hcomp' : ‖iteratedFDeriv ℝ n (g ∘ rootFlowNormalizedArgument σ) q‖ ≤
      (n.factorial : ℝ) * ((2 + Real.pi) * (M + 1)) := by
    simpa only [one_pow, mul_one] using hcomp
  apply hcomp'.trans
  exact (mul_le_mul_of_nonneg_right hfactor hraw0).trans_eq (by ring)

/-- The complete ordinary root-input jets follow from the actual flow
equation and its forward displacement estimate. The low order and loss
are common to every requested finite order and every contraction. -/
theorem n04FlowInverse_normalized_fixed_loss
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ Λ : ℝ, ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ z : Z, p base z ≤ 1 →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations F Θ → N04FlowJetBounds p inputLoss A z 1 Λ Θ →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ 1 → ∀ s : ℕ,
        CSBound s rootInputBox
          ((parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)) ∘
            rootFlowNormalizedArgument σ)
          (B s * (1 + p (s + loss) z)) := by
  choose C hC hnormalized using exists_csBound_rootFlowNormalizedInverse
  obtain ⟨base, loss, htarget⟩ :=
    n04FlowInverse_displacement_fixed_loss hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA Λ
  obtain ⟨D, hD, hinverse⟩ := htarget A hA Λ
  let H : ℕ → ℝ := fun s => ∑ k ∈ Finset.range (s + 1), D k
  have hH (s : ℕ) : 0 ≤ H s := Finset.sum_nonneg (fun k _ => (hD k).le)
  have hDH (s n : ℕ) (hn : n ≤ s) : D n ≤ H s :=
    Finset.single_le_sum (f := D) (fun k _ => (hD k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  let B : ℕ → ℝ := fun s => C s * (1 + H s)
  refine ⟨B, fun s => mul_pos (hC s) (by linarith [hH s]), ?_⟩
  intro z hz F hF hperiod Θ hΘ hforward t ht σ hσ s
  let g : N04FlowPoint → ℝ :=
    parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)
  let M : ℝ := H s * (1 + p (s + loss) z)
  have hstate : 1 ≤ 1 + p (s + loss) z :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  have hM : 0 ≤ M := mul_nonneg (hH s) (zero_le_one.trans hstate)
  have hdisplacement : CSBound s (n04FlowParameterBox ×ˢ (univ : Set ℝ))
      (fun y : N04FlowPoint => g y - y.2) M := by
    intro n hn q hq
    have hraw := hinverse z hz F hF hperiod Θ hΘ hforward t ht q hq.1 n
    apply hraw.trans
    exact mul_le_mul (hDH s n hn)
      (add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_right hn loss)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hH s)
  have hbound := hnormalized s g (contDiff_n04FlowInverse hF hperiod hΘ ht)
    M hM hdisplacement σ hσ
  apply hbound.mono_bound
  calc
    C s * (M + 1) ≤ C s * (M + (1 + p (s + loss) z)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hstate) (hC s).le
    _ = B s * (1 + p (s + loss) z) := by
      dsimp only [M, B]
      ring

end ContinuousFlexibility.Analysis
