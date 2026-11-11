import ContinuousFlexibility.Analysis.N04FlowInverseGeometry
import ContinuousFlexibility.Analysis.NonlinearInverseMaterialBounds
import ContinuousFlexibility.Analysis.ScalarFlowTriangularJets

/-!
# One state loss for the actual parameterized circle inverse

Only positive jets of the original forward family and its actual
angular lower bound are quantitative inputs. The full inverse retains
the external parameters. Its first differential is derived from the
right-inverse equation, and every higher differential follows from the
proved nonlinear inverse polynomial before state interpolation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem parameterizedCircleInverse_positiveJets_fixed_loss
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ z : Z, p base z ≤ 1 →
      ∀ f : P × ℝ → ℝ, ∀ T : ℝ, T ≠ 0 → ContDiff ℝ ∞ f →
      (∀ q : P × ℝ, 0 < deriv (fun θ => f (q.1, θ)) q.2) →
      (∀ v θ, f (v, θ + T) = f (v, θ) + T) →
      ∀ x : P × ℝ,
      κ ≤ deriv (fun θ => f (x.1, θ)) (parameterizedCircleInverse f x) →
      (∀ n : ℕ, 1 ≤ n →
        ‖iteratedFDeriv ℝ n f (x.1, parameterizedCircleInverse f x)‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
      ∀ k : ℕ, 1 ≤ k →
        ‖iteratedFDeriv ℝ k (scalarFamilyLift (parameterizedCircleInverse f)) x‖ ≤
          B k * (1 + p (k + loss) z) := by
  obtain ⟨base, loss, htarget⟩ :=
    nonlinearInverse_positiveJets_le_material hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA κ hκ
  let C : ℕ → ℝ := fun j => 2 + (2 + A (j + 1)) * κ⁻¹ + A (j + 1)
  have hκinv : 0 ≤ κ⁻¹ := (inv_pos.mpr hκ).le
  have hC (j : ℕ) : 1 ≤ C j := by
    have ha := hA (j + 1)
    have hm : 0 ≤ (2 + A (j + 1)) * κ⁻¹ := mul_nonneg (by linarith) hκinv
    dsimp only [C]
    linarith
  have hCA (j : ℕ) : 1 + A (j + 1) ≤ C j := by
    have ha := hA (j + 1)
    have hm : 0 ≤ (2 + A (j + 1)) * κ⁻¹ := mul_nonneg (by linarith) hκinv
    dsimp only [C]
    linarith
  obtain ⟨B, hB, hbound⟩ := htarget C hC
  refine ⟨B, hB, ?_⟩
  intro z hz f T hT hf hpositive hperiod x hangle hraw k hk
  let g : P × ℝ → ℝ := parameterizedCircleInverse f
  let F : P × ℝ → P × ℝ := scalarFamilyLift f
  let G : P × ℝ → P × ℝ := scalarFamilyLift g
  have hg : ContDiff ℝ ∞ g :=
    contDiff_parameterizedCircleInverse hT hf hpositive hperiod
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hG : ContDiff ℝ ∞ G := contDiff_fst.prodMk hg
  obtain ⟨_, hright⟩ := scalarFamilyLift_circleInverse_identities hT hf hpositive hperiod
  have hfg : F ∘ G =ᶠ[𝓝 x] (id : P × ℝ → P × ℝ) :=
    Filter.Eventually.of_forall hright
  let L : (P × ℝ) →L[ℝ] (P × ℝ) := fderiv ℝ G x
  have hL : L.comp (fderiv ℝ F (G x)) = ContinuousLinearMap.id ℝ (P × ℝ) :=
    scalarFamilyLift_circleInverse_fderiv_comp hT hf hpositive hperiod x
  have hLbound : ‖L‖ ≤ C 0 * (1 : ℝ) ^ C 0 * (1 + p (inputLoss + 1) z) := by
    let S : ℝ := 1 + p (inputLoss + 1) z
    have hS : 1 ≤ S := le_add_of_nonneg_right (apply_nonneg _ _)
    have ha : 0 ≤ A 1 := zero_le_one.trans (hA 1)
    have hfirst : ‖fderiv ℝ f (x.1, g x)‖ ≤ A 1 * S := by
      simpa only [norm_iteratedFDeriv_one, S, Nat.add_comm 1 inputLoss] using
        hraw 1 le_rfl
    have hi : ‖L‖ ≤ 1 + (1 + A 1 * S) / κ :=
      parameterizedCircleInverse_lift_fderiv_norm_le hT hf hpositive hperiod x hκ
        (mul_nonneg ha (zero_le_one.trans hS)) hangle hfirst
    have hcoef : 1 + (1 + A 1) * κ⁻¹ ≤ C 0 := by
      dsimp only [C]
      norm_num only [Nat.zero_add]
      nlinarith
    have hpack : 1 + (1 + A 1 * S) / κ ≤ C 0 * S := by
      rw [div_eq_mul_inv]
      calc
        _ ≤ (1 + (1 + A 1) * κ⁻¹) * S := by
          nlinarith [mul_nonneg hκinv (sub_nonneg.mpr hS)]
        _ ≤ C 0 * S := mul_le_mul_of_nonneg_right hcoef (zero_le_one.trans hS)
    simpa only [Real.one_rpow, mul_one, S] using hi.trans hpack
  have hFbound (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) F (G x)‖ ≤
        C j * (1 : ℝ) ^ C j * (1 + p (j + inputLoss + 1) z) := by
    let S : ℝ := 1 + p (j + inputLoss + 1) z
    have hS : 1 ≤ S := le_add_of_nonneg_right (apply_nonneg _ _)
    have horder : (j + 1) + inputLoss = j + inputLoss + 1 := by omega
    have hr : ‖iteratedFDeriv ℝ (j + 1) f (G x)‖ ≤ A (j + 1) * S := by
      simpa only [G, scalarFamilyLift, S, horder] using hraw (j + 1) (by omega)
    have hb : ‖iteratedFDeriv ℝ (j + 1) F (G x)‖ ≤ C j * S := by
      calc
        _ ≤ 1 + ‖iteratedFDeriv ℝ (j + 1) f (G x)‖ :=
          flowJet_augmented_jet_norm_le hf (by omega) (G x)
        _ ≤ 1 + A (j + 1) * S := add_le_add le_rfl hr
        _ ≤ (1 + A (j + 1)) * S := by nlinarith
        _ ≤ C j * S := mul_le_mul_of_nonneg_right (hCA j) (zero_le_one.trans hS)
    simpa only [Real.one_rpow, mul_one, S] using hb
  have result := hbound z hz 1 le_rfl (P × ℝ) (P × ℝ) F G x
    hF.contDiffAt hG.contDiffAt hfg L hL hLbound hFbound k hk
  simpa only [Real.one_rpow, mul_one] using result

end ContinuousFlexibility.Analysis
