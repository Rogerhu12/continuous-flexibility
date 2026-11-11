import ContinuousFlexibility.Analysis.ParameterizedInverseStateJets

/-!
# Actual mixed jets of the inverse flow displacement

The independent flow estimate controls the forward displacement. The
positive first angular Jacobian comes from the original ODE. These
facts give all inverse displacement jets with one low state order and
one loss; no quantitative derivative of the inverse is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem scalarFamily_positiveJet_le_displacement
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} (hn : 1 ≤ n)
    (x : P × ℝ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      ‖iteratedFDeriv ℝ n (fun y : P × ℝ => f y - y.2) x‖ + 1 := by
  have he : f = (fun y : P × ℝ => f y - y.2) + (fun y : P × ℝ => y.2) := by
    funext y
    exact (sub_add_cancel (f y) y.2).symm
  have hjet : iteratedFDeriv ℝ n f x =
      iteratedFDeriv ℝ n (fun y : P × ℝ => f y - y.2) x +
        iteratedFDeriv ℝ n (fun y : P × ℝ => y.2) x := by
    conv_lhs => rw [he]
    exact iteratedFDeriv_add_apply
      ((hf.sub contDiff_snd).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      contDiffAt_snd
  have hp : ‖iteratedFDeriv ℝ n (fun y : P × ℝ => y.2) x‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.coe_snd'] using
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ P ℝ) hn x).trans
        (ContinuousLinearMap.norm_snd_le ℝ P ℝ)
  rw [hjet]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hp)

private theorem scalarFamily_jet_le_lift
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : P × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P × ℝ) :
    ‖iteratedFDeriv ℝ n g x‖ ≤ ‖iteratedFDeriv ℝ n (scalarFamilyLift g) x‖ := by
  let L : (P × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ P ℝ
  have hG : ContDiff ℝ ∞ (scalarFamilyLift g) := contDiff_fst.prodMk hg
  have he : (L : P × ℝ → ℝ) ∘ scalarFamilyLift g = g := by
    funext y
    simp only [L, Function.comp_apply, scalarFamilyLift, ContinuousLinearMap.coe_snd']
  have hb := L.norm_iteratedFDeriv_comp_left (x := x) (n := n) hG.contDiffAt (by simp)
  rw [he] at hb
  exact hb.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_snd_le ℝ P ℝ) (norm_nonneg _))

theorem n04FlowInverse_displacement_fixed_loss
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ Λ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : Z, p base z ≤ 1 →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations F Θ → N04FlowJetBounds p inputLoss A z 1 Λ Θ →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (fun y : N04FlowPoint =>
            parameterizedCircleInverse (fun x : N04FlowPoint => Θ x.1 t x.2) y - y.2) q‖ ≤
          B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, htarget⟩ :=
    parameterizedCircleInverse_positiveJets_fixed_loss
      (P := ℝ × ℝ) hp hI inputLoss
  refine ⟨base, max loss inputLoss, ?_⟩
  intro A hA Λ
  let A' : ℕ → ℝ := fun n => 1 + A n
  have hA' (n : ℕ) : 1 ≤ A' n := le_add_of_nonneg_right (hA n).le
  obtain ⟨C, hC, hbound⟩ := htarget A' hA' (Real.exp (-Λ)) (Real.exp_pos _)
  let B : ℕ → ℝ := fun n => if n = 0 then A 0 else C n + 1
  refine ⟨B, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · simpa only [B, if_pos hn] using hA 0
    · simpa only [B, if_neg hn] using add_pos (hC n) zero_lt_one
  · intro z hz F hF hperiod Θ hΘ hest t ht q hq n
    let f : N04FlowPoint → ℝ := fun y => Θ y.1 t y.2
    let g : N04FlowPoint → ℝ := parameterizedCircleInverse f
    have hf : ContDiff ℝ ∞ f := (hest t ht).1
    have hpos : ∀ y : N04FlowPoint, 0 < deriv (fun θ => f (y.1, θ)) y.2 :=
      fun y => n04Flow_angular_deriv_pos hF hperiod hΘ ht y.1 y.2
    have hper : ∀ v θ, f (v, θ + Real.pi) = f (v, θ) + Real.pi := (hest t ht).2.1
    have hg : ContDiff ℝ ∞ g :=
      contDiff_parameterizedCircleInverse Real.pi_ne_zero hf hpos hper
    have hright : f (q.1, g q) = q.2 :=
      parameterizedCircleInverse_right_inverse Real.pi_ne_zero hf hper q
    have hraw (j : ℕ) :
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => f y - y.2) (q.1, g q)‖ ≤
          A j * (1 + p (j + inputLoss) z) := by
      simpa only [Real.one_rpow, mul_one] using (hest t ht).2.2.2 j (q.1, g q) hq
    by_cases hn : n = 0
    · subst n
      have hb : |g q - q.2| ≤ A 0 * (1 + p inputLoss z) := by
        have hh := hraw 0
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
          hright, Nat.zero_add, abs_sub_comm] using hh
      change ‖iteratedFDeriv ℝ 0 (fun y : N04FlowPoint => g y - y.2) q‖ ≤ _
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, B, if_pos rfl, Nat.zero_add]
      exact hb.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((hp (le_max_right loss inputLoss)) z)) (hA 0).le)
    · have hnpos : 1 ≤ n := by omega
      have hforward (j : ℕ) (hj : 1 ≤ j) :
          ‖iteratedFDeriv ℝ j f (q.1, g q)‖ ≤ A' j * (1 + p (j + inputLoss) z) := by
        apply (scalarFamily_positiveJet_le_displacement hf hj (q.1, g q)).trans
        apply (add_le_add (hraw j) le_rfl).trans
        dsimp only [A']
        nlinarith [apply_nonneg (p (j + inputLoss)) z]
      have hfull : ‖iteratedFDeriv ℝ n (scalarFamilyLift g) q‖ ≤
          C n * (1 + p (n + loss) z) :=
        hbound z hz f Real.pi Real.pi_ne_zero hf hpos hper q
          ((hest t ht).2.2.1 q.1 hq (g q)).1 hforward n hnpos
      have hscalar : ‖iteratedFDeriv ℝ n g q‖ ≤ C n * (1 + p (n + loss) z) :=
        (scalarFamily_jet_le_lift hg n q).trans hfull
      have hsnd : ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => y.2) q‖ ≤ 1 := by
        simpa only [ContinuousLinearMap.coe_snd'] using
          (flowJet_norm_iteratedFDeriv_clm_le
            (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) hnpos q).trans
              (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ)
      have hdisplacement :
          ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => g y - y.2) q‖ ≤
            (C n + 1) * (1 + p (n + loss) z) := by
        have he : (fun y : N04FlowPoint => g y - y.2) =
            g - (fun y : N04FlowPoint => y.2) := by
          funext y
          exact (Pi.sub_apply g (fun x : N04FlowPoint => x.2) y).symm
        rw [he, iteratedFDeriv_sub_apply
          (hg.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) contDiffAt_snd]
        apply (norm_sub_le _ _).trans
        apply (add_le_add hscalar hsnd).trans
        nlinarith [apply_nonneg (p (n + loss)) z]
      change ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => g y - y.2) q‖ ≤ _
      simp only [B, if_neg hn]
      exact hdisplacement.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((hp (Nat.add_le_add_left (le_max_left loss inputLoss) n)) z))
        (add_nonneg (hC n).le zero_le_one))

end ContinuousFlexibility.Analysis
