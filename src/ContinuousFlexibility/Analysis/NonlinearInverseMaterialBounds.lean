module

public import ContinuousFlexibility.Analysis.NonlinearInversePolynomialBounds
public import ContinuousFlexibility.Analysis.FlowJetMaterialClosure

/-!
# A fixed material loss for actual nonlinear inverse jets

The input consists of bounds on the genuine inverse first derivative
and the original forward higher derivatives. Polynomial inverse jets
are expanded before applying state interpolation, so one low order and
one derivative loss work at every positive order.
-/

@[expose] public section

noncomputable section

universe u v

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- All positive inverse jets obey a single high-seminorm material bound.
The low order and loss precede every raw coefficient sequence, while the
output constants precede the state, envelope, and actual maps. -/
theorem nonlinearInverse_positiveJets_le_material
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ z : Z, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ (E : Type u) (F : Type v)
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ (f : E → F) (g : F → E) (x : F),
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        f ∘ g =ᶠ[𝓝 x] (id : F → F) →
      ∀ L : F →L[ℝ] E,
        L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E →
        ‖L‖ ≤ A 0 * W ^ (A 0) * (1 + p (inputLoss + 1) z) →
        (∀ k : ℕ, 1 ≤ k →
          ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤
            A k * W ^ (A k) * (1 + p (k + inputLoss + 1) z)) →
        ∀ k : ℕ, 1 ≤ k →
          ‖iteratedFDeriv ℝ k g x‖ ≤
            B k * W ^ (B k) * (1 + p (k + loss) z) := by
  classical
  choose P hP hbound using
    (fun n => exists_nonlinearInverse_spatialJet_polynomial.{u, v} n)
  obtain ⟨base, loss, hmaterial⟩ :=
    flowJetPolynomial_le_material_one_high hp hI (inputLoss + 1)
  refine ⟨base, loss, ?_⟩
  intro A hA
  have hC (n : ℕ) :
      ∃ C : ℝ, 0 < C ∧ ∀ z : Z, p base z ≤ 1 →
        ∀ W : ℝ, 1 ≤ W →
          flowJetPolynomialEval (P n)
            (fun k => A k * W ^ (A k) * (1 + p (k + (inputLoss + 1)) z)) ≤
            C * W ^ C * (1 + p ((n + 1) + loss) z) :=
    hmaterial (n + 1) (P n) ((hP n).mono (Nat.le_succ n)) A hA
  choose C hCpos hCb using hC
  let B : ℕ → ℝ := fun k => if k = 0 then 1 else C (k - 1)
  refine ⟨B, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · simp only [B, if_pos hk, zero_lt_one]
    · simpa only [B, if_neg hk] using hCpos (k - 1)
  · intro z hz W hW E F _ _ _ _ f g x hf hg hfg L hL hLbound hraw k hk
    let M : ℕ → ℝ := fun j =>
      A j * W ^ (A j) * (1 + p (j + (inputLoss + 1)) z)
    have hM (j : ℕ) : 0 ≤ M j :=
      mul_nonneg
        (mul_nonneg (zero_le_one.trans (hA j)) (Real.rpow_nonneg (zero_le_one.trans hW) _))
        (add_nonneg zero_le_one (apply_nonneg _ _))
    have hLbound' : ‖L‖ ≤ M 0 := by
      simpa only [M, Nat.zero_add] using hLbound
    have hraw' (j : ℕ) (hj : 1 ≤ j) :
        ‖iteratedFDeriv ℝ (j + 1) f (g x)‖ ≤ M j := by
      simpa only [M, Nat.add_assoc] using hraw j hj
    have hjets := hbound (k - 1) M hM E F f g x hf hg hfg L hL hLbound' hraw'
    have horder : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [horder] at hjets
    have hpack := hCb (k - 1) z hz W hW
    rw [horder] at hpack
    have hk0 : k ≠ 0 := by omega
    calc
      ‖iteratedFDeriv ℝ k g x‖ ≤ flowJetPolynomialEval (P (k - 1)) M := hjets
      _ ≤ C (k - 1) * W ^ (C (k - 1)) * (1 + p (k + loss) z) := hpack
      _ = B k * W ^ (B k) * (1 + p (k + loss) z) := by
        simp only [B, if_neg hk0]

end ContinuousFlexibility.Analysis
