module

public import ContinuousFlexibility.Analysis.PlanarInverseDerivativeBound
public import ContinuousFlexibility.Analysis.NonlinearInverseMaterialBounds

/-!
# Actual planar inverse jets from a Jacobian lower bound

The first inverse derivative is obtained from the actual inverse germ,
four forward matrix entries, and |J|≥κ. Its high state factor remains
linear. The already proved nonlinear inverse polynomial estimate then
controls all positive inverse jets; no inverse jet estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The low order and fixed loss precede the Jacobian lower bound and
all component constants. Both inverse identities are genuine local
germs; only the forward positive jets are quantitative inputs. -/
theorem planarInverse_positiveJets_of_jacobian_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ F G : PolarPoint → PolarPoint, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ F (G x) → ContDiffAt ℝ ∞ G x →
        F ∘ G =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) →
        G ∘ F =ᶠ[𝓝 (G x)] (id : PolarPoint → PolarPoint) →
        κ ≤ |planeJacobian F (G x)| →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G x)‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n G x‖ ≤
          B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hinverse⟩ := nonlinearInverse_positiveJets_le_material hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA κ hκ
  have hA0 (n : ℕ) : 0 ≤ A n := zero_le_one.trans (hA n)
  let R (n : ℕ) : ℝ := 1 + A (n + 1) + 2 * A 1 / κ
  have hR (n : ℕ) : 1 ≤ R n := by
    dsimp only [R]
    have hquot : 0 ≤ 2 * A 1 / κ := div_nonneg (mul_nonneg (by norm_num) (hA0 1)) hκ.le
    linarith [hA0 (n + 1)]
  have hAR (n : ℕ) : A (n + 1) ≤ R n := by
    dsimp only [R]
    have hquot : 0 ≤ 2 * A 1 / κ := div_nonneg (mul_nonneg (by norm_num) (hA0 1)) hκ.le
    linarith
  have hfirstR : 2 * A 1 / κ ≤ R 0 := by
    dsimp only [R]
    linarith [hA0 (0 + 1)]
  obtain ⟨B, hB, hbound⟩ := hinverse R hR
  refine ⟨B, hB, ?_⟩
  intro z hz F G x hF hG hright hleft hJ hraw n hn
  have hFx : F (G x) = x := hright.eq_of_nhds
  have hFd : DifferentiableAt ℝ F (G x) := hF.differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G (F (G x)) := by
    rw [hFx]
    exact hG.differentiableAt (by simp)
  let L : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ G x
  have hL : L.comp (fderiv ℝ F (G x)) = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = (fderiv ℝ G (F (G x))).comp (fderiv ℝ F (G x)) := by rw [hFx]
      _ = fderiv ℝ (G ∘ F) (G x) := (fderiv_comp (G x) hGd hFd).symm
      _ = fderiv ℝ (id : PolarPoint → PolarPoint) (G x) := hleft.fderiv_eq
      _ = _ := by rw [fderiv_id]
  let S : ℝ := 1 + p (inputLoss + 1) z
  have hS : 0 ≤ S := add_nonneg zero_le_one (apply_nonneg _ _)
  let M : ℝ := A 1 * S
  have hfirst : ‖fderiv ℝ F (G x)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one, M, S, Nat.add_comm 1 inputLoss] using hraw 1 le_rfl
  have hcolumn (v : PolarPoint) (hv : ‖v‖ ≤ 1) :
      ‖fderiv ℝ F (G x) v‖ ≤ M := by
    exact ((fderiv ℝ F (G x)).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans
        (by simpa only [mul_one] using hfirst))
  have hcolR := hcolumn (1, 0) (by norm_num [Prod.norm_def])
  have hcolT := hcolumn (0, 1) (by norm_num [Prod.norm_def])
  have h11 : |(fderiv ℝ F (G x) (1, 0)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolR
  have h12 : |(fderiv ℝ F (G x) (0, 1)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolT
  have h21 : |(fderiv ℝ F (G x) (1, 0)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolR
  have h22 : |(fderiv ℝ F (G x) (0, 1)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolT
  have hLnorm : ‖L‖ ≤ 2 * M / κ := by
    have he := fderiv_inverse_norm_le_of_germ hFd hGd hleft hκ hJ h11 h12 h21 h22
    simpa only [hFx, L] using he
  have hLbound : ‖L‖ ≤ R 0 * (1 : ℝ) ^ R 0 * (1 + p (inputLoss + 1) z) := by
    have he : 2 * M / κ = (2 * A 1 / κ) * S := by dsimp only [M]; ring
    simpa only [Real.one_rpow, mul_one, S] using
      hLnorm.trans (he.trans_le (mul_le_mul_of_nonneg_right hfirstR hS))
  have hforward (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) F (G x)‖ ≤
        R k * (1 : ℝ) ^ R k * (1 + p (k + inputLoss + 1) z) := by
    have he := (hraw (k + 1) (by omega)).trans
      (mul_le_mul_of_nonneg_right (hAR k)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
    simpa only [Real.one_rpow, mul_one,
      show k + 1 + inputLoss = k + inputLoss + 1 by omega] using he
  simpa only [Real.one_rpow, mul_one] using
    hbound z hz 1 le_rfl PolarPoint PolarPoint F G x hF hG hright
      L hL hLbound hforward n hn

end ContinuousFlexibility.Analysis
