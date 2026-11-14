module

public import ContinuousFlexibility.Analysis.NonlinearInverseMaterialBounds
public import ContinuousFlexibility.Analysis.FlowJetLinearization
public import ContinuousFlexibility.Analysis.ParameterizedScalarInverse

/-!
# Material jets of an actual scalar inverse displacement

The inverse is identified by its true two-sided identities. Its first
differential is bounded separately, and every higher differential is
obtained from the existing nonlinear inverse polynomial. The zeroth
displacement is transported by the right-inverse identity itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Smoothness of an actual right inverse follows from the scalar implicit
theorem. No continuity or smoothness of that inverse is an input. -/
theorem contDiff_scalar_rightInverse_of_deriv_pos
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ θ, 0 < deriv f θ) (hright : ∀ θ, f (g θ) = θ) :
    ContDiff ℝ ∞ g := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.2) :=
    contDiff_parameterized_scalar_rightInverse
      (F := fun q : ℝ × ℝ => f q.2) (hf.comp contDiff_snd)
      (fun q => hpos q.2) (fun q => hright q.2)
  have hc : ContDiff ℝ ∞ (fun θ : ℝ => ((0 : ℝ), θ)) :=
    contDiff_const.prodMk contDiff_id
  exact hG.comp hc

private theorem scalarInverse_fderiv_comp
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hright : ∀ θ, f (g θ) = θ) (hleft : ∀ θ, g (f θ) = θ) (θ : ℝ) :
    (fderiv ℝ g θ).comp (fderiv ℝ f (g θ)) = ContinuousLinearMap.id ℝ ℝ := by
  have he : g ∘ f = id := funext hleft
  calc
    _ = (fderiv ℝ g (f (g θ))).comp (fderiv ℝ f (g θ)) := by rw [hright θ]
    _ = fderiv ℝ (g ∘ f) (g θ) :=
      (fderiv_comp (g θ) (hg.differentiable (by simp) _)
        (hf.differentiable (by simp) _)).symm
    _ = _ := by rw [he, fderiv_id]

/-- The complete scalar estimate is named so that concrete state spaces
can instantiate it without expanding their entire grading during choice. -/
def ScalarInverseDisplacementEstimate
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (low inputLoss loss : ℕ) (A B : ℕ → ℝ) : Prop :=
  ∀ z : E, p low z ≤ 1 →
    ∀ f g : ℝ → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    (∀ θ, f (g θ) = θ) → (∀ θ, g (f θ) = θ) →
    (∀ θ, ‖fderiv ℝ g θ‖ ≤ 2) →
    (∀ n : ℕ, 2 ≤ n → ∀ θ,
      ‖iteratedFDeriv ℝ n f θ‖ ≤ A n * (1 + p (n + inputLoss) z)) →
    (∀ θ, |f θ - θ| ≤ A 0 * (1 + p inputLoss z)) →
    ∀ n θ, ‖iteratedFDeriv ℝ n (fun η => g η - η) θ‖ ≤
      B n * (1 + p (n + loss) z)

/-- A fixed loss for every actual inverse displacement jet. Only forward
jets of order at least two, the true inverse first differential, and the
forward zeroth displacement are quantitative inputs. The low order and
loss precede all numerical majorants and the maps themselves. -/
theorem scalarInverse_displacement_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        ScalarInverseDisplacementEstimate p low inputLoss loss A B := by
  obtain ⟨low, loss, htarget⟩ := nonlinearInverse_positiveJets_le_material hp hI inputLoss
  refine ⟨low, max loss inputLoss, ?_⟩
  intro A hA
  let C : ℕ → ℝ := fun j => 2 + A (j + 1)
  have hC (j : ℕ) : 1 ≤ C j := by
    have ha := hA (j + 1)
    dsimp only [C]
    linarith
  obtain ⟨D, hD, hbound⟩ := htarget C hC
  let B : ℕ → ℝ := fun n => if n = 0 then A 0 else D n + 1
  have hB (n : ℕ) : 0 < B n := by
    by_cases hn : n = 0
    · simpa only [B, if_pos hn] using zero_lt_one.trans_le (hA 0)
    · simpa only [B, if_neg hn] using add_pos (hD n) zero_lt_one
  refine ⟨B, hB, ?_⟩
  intro z hz f g hf hg hright hleft hfirst hraw hzero n θ
  have hgrade (k : ℕ) (j : ℕ) (hj : j ≤ max loss inputLoss) :
      1 + p (k + j) z ≤ 1 + p (k + max loss inputLoss) z :=
    add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_left hj k)) z)
  by_cases hn : n = 0
  · subst n
    have he : |g θ - θ| = |f (g θ) - g θ| := by
      rw [hright θ, abs_sub_comm]
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, he]
    exact (hzero (g θ)).trans (by
      simpa only [B, if_pos rfl, Nat.zero_add] using
        mul_le_mul_of_nonneg_left (hgrade 0 inputLoss (le_max_right _ _))
          (zero_le_one.trans (hA 0)))
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hfg : f ∘ g =ᶠ[𝓝 θ] (id : ℝ → ℝ) := Eventually.of_forall hright
    have hL : ‖fderiv ℝ g θ‖ ≤
        C 0 * (1 : ℝ) ^ C 0 * (1 + p (inputLoss + 1) z) := by
      have hp0 := apply_nonneg (p (inputLoss + 1)) z
      have ha := hA 1
      have hf0 := hfirst θ
      simp only [Real.one_rpow, mul_one, C, Nat.zero_add]
      nlinarith
    have hraw' (j : ℕ) (hj : 1 ≤ j) :
        ‖iteratedFDeriv ℝ (j + 1) f (g θ)‖ ≤
          C j * (1 : ℝ) ^ C j * (1 + p (j + inputLoss + 1) z) := by
      have horder : (j + 1) + inputLoss = j + inputLoss + 1 := by omega
      have hb := hraw (j + 1) (by omega) (g θ)
      rw [horder] at hb
      simp only [Real.one_rpow, mul_one]
      exact hb.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
        (add_nonneg zero_le_one (apply_nonneg _ _)))
    have hi : ‖iteratedFDeriv ℝ n g θ‖ ≤ D n * (1 + p (n + loss) z) := by
      simpa only [Real.one_rpow, mul_one] using
        hbound z hz 1 le_rfl ℝ ℝ f g θ hf.contDiffAt hg.contDiffAt hfg
          (fderiv ℝ g θ) (scalarInverse_fderiv_comp hf hg hright hleft θ)
          hL hraw' n hnpos
    have hi' := hi.trans (mul_le_mul_of_nonneg_left
      (hgrade n loss (le_max_left _ _)) (hD n).le)
    have hid : ‖iteratedFDeriv ℝ n (id : ℝ → ℝ) θ‖ ≤ 1 :=
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℝ) hnpos θ).trans
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
    have he : (fun η : ℝ => g η - η) = g - id := by funext η; rfl
    rw [he, iteratedFDeriv_sub_apply
      (hg.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (contDiffAt_id.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
    apply (norm_sub_le _ _).trans
    apply (add_le_add hi' hid).trans
    have hp0 := apply_nonneg (p (n + max loss inputLoss)) z
    simp only [B, if_neg hn]
    nlinarith

end ContinuousFlexibility.Analysis
