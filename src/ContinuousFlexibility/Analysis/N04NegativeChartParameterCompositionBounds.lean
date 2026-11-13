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

private theorem composition_product_bound
    (n K D : ℕ) (hn : 0 < n) {κ u : Q → ℝ}
    (hκs : ContDiff ℝ ∞ κ) (hus : ContDiff ℝ ∞ u)
    (x : Q) {W M R ρ : ℝ} (hW : 0 ≤ W) (hM : 1 ≤ M)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ)
    (hκ : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j κ x‖ ≤ M * ρ ^ j)
    (hu : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j u x‖ ≤ W * M * ρ ^ (D + j))
    (j : ℕ) (hj : j ≤ K) :
    ‖iteratedFDeriv ℝ j (fun y => κ y * u y) x‖ ≤
      (2 : ℝ) ^ K * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) := by
  have hCp : 0 ≤ (2 : ℝ) ^ K := pow_nonneg (by norm_num) _
  have hup (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l u x‖ ≤ (W * M * ρ ^ D) * ρ ^ l := by
    simpa only [pow_add, mul_assoc] using hu l (hl.trans hj)
  have hp := n04NegativeGeometry_weighted_product_jet_le hκs.contDiffAt hus.contDiffAt
    (zero_le_one.trans hM)
    (mul_nonneg (mul_nonneg hW (zero_le_one.trans hM)) (pow_nonneg (zero_le_one.trans hρ) _))
    (zero_le_one.trans hρ) hj (fun l hl => hκ l (hl.trans hj)) hup
  have hMR : 1 ≤ M * R := one_le_mul_of_one_le_of_one_le hM hR
  have hMM : M ^ 2 ≤ (M * R) ^ (n + 1) :=
    (pow_le_pow_left₀ (zero_le_one.trans hM)
      (le_mul_of_one_le_right (zero_le_one.trans hM) hR) 2).trans
      (pow_le_pow_right₀ hMR (by omega))
  have hDD : D + j ≤ D * (n + 1) + j := by
    have hh := Nat.mul_le_mul_left D (show 1 ≤ n + 1 by omega)
    simpa only [Nat.mul_one] using Nat.add_le_add_right hh j
  calc
    _ ≤ (2 : ℝ) ^ K * M * (W * M * ρ ^ D) * ρ ^ j := hp
    _ = (2 : ℝ) ^ K * W * M ^ 2 * ρ ^ (D + j) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left hMM (mul_nonneg hCp hW))
      (pow_le_pow_right₀ hρ hDD) (pow_nonneg (zero_le_one.trans hρ) _)
      (mul_nonneg (mul_nonneg hCp hW) (pow_nonneg (zero_le_one.trans hMR) _))

private theorem composition_sum_bound
    (n K D : ℕ) (hn : 0 < n) {κ u F : Q → ℝ}
    (hκs : ContDiff ℝ ∞ κ) (hus : ContDiff ℝ ∞ u) (hFs : ContDiff ℝ ∞ F)
    (x : Q) {W M R ρ Cf : ℝ} (hW : 0 ≤ W) (hM : 1 ≤ M)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ)
    (hκ : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j κ x‖ ≤ M * ρ ^ j)
    (hu : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j u x‖ ≤ W * M * ρ ^ (D + j))
    (hF : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j F x‖ ≤
      Cf * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j))
    (j : ℕ) (hj : j ≤ K) :
    ‖iteratedFDeriv ℝ j (fun y => κ y * u y + F y) x‖ ≤
      (1 + (2 : ℝ) ^ K + Cf) * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) := by
  have hp := composition_product_bound n K D hn hκs hus x hW hM hR hρ hκ hu j hj
  change ‖iteratedFDeriv ℝ j ((fun y => κ y * u y) + F) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((hκs.mul hus).contDiffAt.of_le (by simp))
    (hFs.contDiffAt.of_le (by simp))]
  have hMR : 0 ≤ M * R := mul_nonneg (zero_le_one.trans hM) (zero_le_one.trans hR)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => κ y * u y) x‖ + ‖iteratedFDeriv ℝ j F x‖ := norm_add_le _ _
    _ ≤ ((2 : ℝ) ^ K + Cf) * W * (M * R) ^ (n + 1) * ρ ^ (D * (n + 1) + j) :=
      (add_le_add hp (hF j hj)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by linarith : (2 : ℝ) ^ K + Cf ≤ 1 + (2 : ℝ) ^ K + Cf) hW)
        (pow_nonneg hMR _)) (pow_nonneg (zero_le_one.trans hρ) _)

set_option diagnostics true in
set_option backward.isDefEq.respectTransparency true in
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
  have hex := n04NegativeChart_actualForcing_weighted_prefix (E := E) (Q := Q) n K
  let Cf := hex.choose
  have hCf := hex.choose_spec.1
  have hCp : 0 ≤ (2 : ℝ) ^ K := pow_nonneg (by norm_num) _
  refine ⟨1 + (2 : ℝ) ^ K + Cf, by linarith only [hCp, hCf], ?_⟩
  intro G Θ hG J hΘ γ α hγ hα v t x W M R ρ D hW hWR hM hR hρ hκ hhead hlower
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
  have hu (l : ℕ) (hl : l ≤ K) :
      ‖iteratedFDeriv ℝ l u x‖ ≤ W * M * ρ ^ (D + l) := by
    simpa only [Function.comp_id, u] using hlower n hn le_rfl id l hl
  have hmarked := n04NegativeChart_actualForcing_marked_factors J hΘ hn K D γ α v t x
    hW hWR hM hR hρ hhead (fun k hk hkn e l hl => hlower k hk hkn.le e l hl)
  have hf := hex.choose_spec.2 (G := G) (Θ := Θ) hG J hΘ γ α hγ hα v t x D hW
    (one_le_mul_of_one_le_of_one_le hM hR) hρ hmarked
  have he : (fun y : Q =>
      flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) n (γ y) v (t, α y)) =
      fun y => κ y * u y + F y := by
    funext y
    dsimp only [κ, u, F]
    rw [flowVariationForcing_eq_source_sub hG J hΘ hn]
    ring
  rw [he]
  exact composition_sum_bound n K D hn hκs hus hFs x hW hM hR hρ hκ hu hf

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_parameterComposition_positive_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_parameterComposition_positive_prefix
