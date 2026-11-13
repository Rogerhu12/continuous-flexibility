import ContinuousFlexibility.Analysis.N04NegativeChartVariationSelection

/-!
# Positive parameter jets of a scalar function along the same flow

The exact parameter composition identity consists of its linear highest
variation and the canonical finite forcing sum. A marked height weight
survives both terms. No differential equation for the outer scalar
function is used, so the result also applies to the endpoint label.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The constant is fixed before all representatives and evaluated
points. All losses in state order remain in the power `D`, separately
from the requested spatial order. -/
theorem n04NegativeChart_parameterComposition_positive_prefix
    (n K : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {G Θ : E × PolarPoint → ℝ},
      ∀ (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
        (hΘ : ContDiff ℝ ∞ Θ) (γ : Q → E) (α : Q → ℝ),
      ContDiff ℝ ∞ γ → ContDiff ℝ ∞ α →
      ∀ (v : Fin n → E) (t : ℝ) (x : Q) {W M R ρ : ℝ} (D : ℕ),
      0 ≤ W → W ≤ R → 1 ≤ M → 1 ≤ R → 1 ≤ ρ →
      (∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
        flowVariationCoefficient G Θ (γ y) (t, α y)) x‖ ≤ M * ρ ^ j) →
      (∀ d : FlowForcingChoice n, ∀ j, j ≤ K →
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d 0 (α y)) x‖ ≤
            parameterHeightWeight W d.2.card * M * ρ ^ (D + j)) →
      (∀ k, 0 < k → k ≤ n → ∀ e : Fin k → Fin n, ∀ j, j ≤ K →
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          flowParameterField Θ k (γ y) (v ∘ e) (t, α y)) x‖ ≤
            W * M * ρ ^ (D + j)) →
      ∀ j, j ≤ K →
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) n
            (γ y) v (t, α y)) x‖ ≤
          C * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) := by
  obtain ⟨Cf, hCf, hforcing⟩ := n04NegativeChart_actualForcing_weighted_prefix (E := E) (Q := Q) n K
  let Cp : ℝ := (2 : ℝ) ^ K
  have hCp : 0 ≤ Cp := pow_nonneg (by norm_num) _
  refine ⟨1 + Cp + Cf, by dsimp only [Cp]; linarith only [hCp, hCf], ?_⟩
  intro G Θ hG J hΘ γ α hγ hα v t x W M R ρ D hW hWR hM hR hρ hκ hhead hlower j hj
  let κ : Q → ℝ := fun y => flowVariationCoefficient G Θ (γ y) (t, α y)
  let u : Q → ℝ := fun y => flowParameterField Θ n (γ y) v (t, α y)
  let F : Q → ℝ := fun y => flowVariationForcing J hΘ n (γ y) v (t, α y)
  have hκs : ContDiff ℝ ∞ κ :=
    (n04NegativeChart_flowCoefficient_joint_contDiff hG hΘ).comp
      (hγ.prodMk (contDiff_const.prodMk hα))
  have hus : ContDiff ℝ ∞ u :=
    (n04NegativeChart_flowParameterField_joint_contDiff hΘ n v).comp
      (hγ.prodMk (contDiff_const.prodMk hα))
  have hFs : ContDiff ℝ ∞ F :=
    (n04NegativeChart_flowForcing_joint_contDiff hG J hΘ hn v).comp
      (hγ.prodMk (contDiff_const.prodMk hα))
  have hu (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l u x‖ ≤ (W * M * ρ ^ D) * ρ ^ l := by
    have hh := hlower n hn le_rfl id l (hl.trans hj)
    simpa only [Function.comp_id, u, pow_add, mul_assoc] using hh
  have hproduct := n04NegativeGeometry_weighted_product_jet_le hκs.contDiffAt hus.contDiffAt
    (zero_le_one.trans hM)
    (mul_nonneg (mul_nonneg hW (zero_le_one.trans hM)) (pow_nonneg (zero_le_one.trans hρ) _))
    (zero_le_one.trans hρ) hj (fun l hl => hκ l (hl.trans hj)) hu
  have hMR : 1 ≤ M * R := one_le_mul_of_one_le_of_one_le hM hR
  have hMM : M ^ 2 ≤ (M * R) ^ (n + 1) :=
    (pow_le_pow_left₀ (zero_le_one.trans hM)
      (le_mul_of_one_le_right (zero_le_one.trans hM) hR) 2).trans
      (pow_le_pow_right₀ hMR (by omega))
  have hDD : D + j ≤ D * (n + 1) + j := by
    have hh := Nat.mul_le_mul_left D (show 1 ≤ n + 1 by omega)
    simpa only [Nat.mul_one] using Nat.add_le_add_right hh j
  have hp : ‖iteratedFDeriv ℝ j (fun y => κ y * u y) x‖ ≤
      Cp * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) := by
    calc
      _ ≤ (2 : ℝ) ^ K * M * (W * M * ρ ^ D) * ρ ^ j := hproduct
      _ = Cp * W * M ^ 2 * ρ ^ (D + j) := by rw [pow_add]; dsimp only [Cp]; ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left hMM (mul_nonneg hCp hW))
        (pow_le_pow_right₀ hρ hDD) (pow_nonneg (zero_le_one.trans hρ) _)
        (mul_nonneg (mul_nonneg hCp hW) (pow_nonneg (zero_le_one.trans hMR) _))
  have hmarked := n04NegativeChart_actualForcing_marked_factors J hΘ hn K D γ α v t x
    hW hWR hM hR hρ hhead
    (fun k hk hkn e l hl => hlower k hk hkn.le e l hl)
  have hf := hforcing hG J hΘ γ α hγ hα v t x D hW hMR hρ hmarked j hj
  have he : (fun y : Q =>
      flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) n (γ y) v (t, α y)) =
      fun y => κ y * u y + F y := by
    funext y
    have hh := flowVariationForcing_eq_source_sub hG J hΘ hn (γ y) v (t, α y)
    change _ = _ * _ + _
    dsimp only [κ, u, F]
    linarith only [hh]
  rw [he, iteratedFDeriv_add_apply ((hκs.mul hus).contDiffAt.of_le (by simp))
    (hFs.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => κ y * u y) x‖ + ‖iteratedFDeriv ℝ j F x‖ := norm_add_le _ _
    _ ≤ (Cp + Cf) * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) :=
      (add_le_add hp hf).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by linarith : Cp + Cf ≤ 1 + Cp + Cf) hW)
        (pow_nonneg (zero_le_one.trans hMR) _)) (pow_nonneg (zero_le_one.trans hρ) _)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_parameterComposition_positive_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_parameterComposition_positive_prefix
