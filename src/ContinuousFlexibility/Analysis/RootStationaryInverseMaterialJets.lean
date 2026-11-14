import ContinuousFlexibility.Analysis.RootStationaryMaterialJets
import ContinuousFlexibility.Analysis.ParameterizedInverseStateJets

/-!
# Actual inverse jets on the stationary root axis

At zero parameters the actual root flow is the identity in the angular
variable. Its inverse therefore fixes the same point and the original
angular derivative is exactly one. The first inverse differential is
derived from the true inverse identity; the existing inverse polynomial
then controls all positive jets with one material loss. No inverse flow
jet or inverse angular lower bound is supplied as a quantitative input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem stationaryInverse_weight_pack
    {a W S : ℝ} (ha : 0 ≤ a) (hW : 1 ≤ W) (hS : 1 ≤ S) :
    2 + a * W ^ a * S ≤ (3 + a) * W ^ (3 + a) * S := by
  have hp : 1 ≤ W ^ a := Real.one_le_rpow hW ha
  have hprod : 1 ≤ W ^ a * S := one_le_mul_of_one_le_of_one_le hp hS
  have ha' : a ≤ 3 + a := by linarith
  calc
    _ ≤ (2 + a) * W ^ a * S := by nlinarith
    _ ≤ (3 + a) * W ^ (3 + a) * S :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (by linarith)
          (Real.rpow_le_rpow_of_exponent_le hW ha')
          (Real.rpow_nonneg (zero_le_one.trans hW) _) (by linarith))
        (zero_le_one.trans hS)

/-- The inverse is the actual chosen pointwise circle inverse. Its jets
are proved from the original drift and factored-speed jets at the root,
with the common low order and loss selected before those envelopes. -/
theorem rootRegularizedFlow_zero_inverseJets_le_material
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
        (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRegularizedField d c) Θ →
      ∀ θ : ℝ,
      (∀ n, ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      (∀ n, ‖iteratedFDeriv ℝ n c (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n →
        ‖iteratedFDeriv ℝ n
          (parameterizedCircleInverse (fun y : N04FlowPoint => Θ y.1 t y.2))
            ((0, 0), θ)‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) := by
  obtain ⟨flowBase, flowLoss, hflow⟩ :=
    rootRegularizedFlow_zero_positiveJets_le_material hp hI inputLoss
  obtain ⟨inverseBase, inverseLoss, hinverse⟩ :=
    nonlinearInverse_positiveJets_le_material hp hI flowLoss
  refine ⟨max flowBase inverseBase, inverseLoss, ?_⟩
  intro A hA
  obtain ⟨D, hD, hforward⟩ := hflow A hA
  let C : ℕ → ℝ := fun n => 3 + D n
  have hC (n : ℕ) : 1 ≤ C n := by
    dsimp only [C]
    linarith [hD n]
  obtain ⟨B, hB, hbound⟩ := hinverse C hC
  refine ⟨B, hB, ?_⟩
  intro z hz W hW d c hd hc hdperiod hcperiod Θ hΘ θ hdb hcb t ht n hn
  have hzF : p flowBase z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzI : p inverseBase z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hfield := contDiff_rootRegularizedField hd hc
  have hperiod := rootRegularizedField_periodic hdperiod hcperiod
  let f : N04FlowPoint → ℝ := fun y => Θ y.1 t y.2
  let g : N04FlowPoint → ℝ := parameterizedCircleInverse f
  let F : N04FlowPoint → N04FlowPoint := scalarFamilyLift f
  let G : N04FlowPoint → N04FlowPoint := scalarFamilyLift g
  let q : N04FlowPoint := ((0, 0), θ)
  have hf : ContDiff ℝ ∞ f := n04Flow_contDiff_slice hfield hperiod hΘ ht
  have hpositive : ∀ y : N04FlowPoint, 0 < deriv (fun η => f (y.1, η)) y.2 :=
    fun y => n04Flow_angular_deriv_pos hfield hperiod hΘ ht y.1 y.2
  have hfperiod : ∀ v η, f (v, η + Real.pi) = f (v, η) + Real.pi :=
    fun v η => n04Flow_period_add hfield hperiod hΘ v η ht
  have hg : ContDiff ℝ ∞ g :=
    contDiff_parameterizedCircleInverse Real.pi_ne_zero hf hpositive hfperiod
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hG : ContDiff ℝ ∞ G := contDiff_fst.prodMk hg
  have hzero (η : ℝ) : f ((0, 0), η) = η :=
    rootRegularizedFlow_zero_parameters hΘ.1 hΘ.2 η ht
  have hgzero : g q = θ := by
    have hh := parameterizedCircleInverse_right_inverse Real.pi_ne_zero hf hfperiod q
    change f ((0, 0), g q) = θ at hh
    simpa only [hzero] using hh
  have hGzero : G q = q := by
    change ((0, 0), g q) = ((0, 0), θ)
    rw [hgzero]
  have hangle : (1 : ℝ) ≤ deriv (fun η => f (q.1, η)) (g q) := by
    have he : (fun η => f (q.1, η)) = (id : ℝ → ℝ) := funext hzero
    simpa only [he, deriv_id] using (le_rfl : (1 : ℝ) ≤ 1)
  have hjet (j : ℕ) : ‖iteratedFDeriv ℝ (j + 1) f q‖ ≤
      D j * W ^ (D j) * (1 + p (j + 1 + flowLoss) z) :=
    hforward z hzF W hW d c hd hc hdperiod hcperiod Θ hΘ θ hdb hcb j t ht
  obtain ⟨_, hright⟩ :=
    scalarFamilyLift_circleInverse_identities Real.pi_ne_zero hf hpositive hfperiod
  have hfg : F ∘ G =ᶠ[𝓝 q] (id : N04FlowPoint → N04FlowPoint) :=
    Filter.Eventually.of_forall hright
  let J : N04FlowPoint →L[ℝ] N04FlowPoint := fderiv ℝ G q
  have hJ : J.comp (fderiv ℝ F (G q)) = ContinuousLinearMap.id ℝ N04FlowPoint :=
    scalarFamilyLift_circleInverse_fderiv_comp Real.pi_ne_zero hf hpositive hfperiod q
  have hJbound : ‖J‖ ≤ C 0 * W ^ (C 0) * (1 + p (flowLoss + 1) z) := by
    let S : ℝ := 1 + p (flowLoss + 1) z
    have hS : 1 ≤ S := le_add_of_nonneg_right (apply_nonneg _ _)
    have hfirst : ‖fderiv ℝ f (q.1, g q)‖ ≤ D 0 * W ^ (D 0) * S := by
      rw [hgzero]
      change ‖fderiv ℝ f q‖ ≤ _
      have h0 : ‖iteratedFDeriv ℝ 1 f q‖ ≤
          D 0 * W ^ (D 0) * (1 + p (1 + flowLoss) z) := hjet 0
      rw [norm_iteratedFDeriv_one, Nat.add_comm 1 flowLoss] at h0
      exact h0
    have hM : 0 ≤ D 0 * W ^ (D 0) * S :=
      mul_nonneg (mul_nonneg (hD 0).le
        (Real.rpow_nonneg (zero_le_one.trans hW) _)) (zero_le_one.trans hS)
    have hi := parameterizedCircleInverse_lift_fderiv_norm_le Real.pi_ne_zero
      hf hpositive hfperiod q zero_lt_one hM hangle hfirst
    have hpck := stationaryInverse_weight_pack (hD 0).le hW hS
    have he : 1 + (1 + D 0 * W ^ (D 0) * S) / 1 =
        2 + D 0 * W ^ (D 0) * S := by ring
    rw [he] at hi
    exact hi.trans hpck
  have hFbound (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) F (G q)‖ ≤
        C j * W ^ (C j) * (1 + p (j + flowLoss + 1) z) := by
    have hs : 1 ≤ 1 + p (j + flowLoss + 1) z :=
      le_add_of_nonneg_right (apply_nonneg _ _)
    have ho : j + 1 + flowLoss = j + flowLoss + 1 := by omega
    have hr : ‖iteratedFDeriv ℝ (j + 1) f (G q)‖ ≤
        D j * W ^ (D j) * (1 + p (j + flowLoss + 1) z) := by
      simpa only [hGzero, ho] using hjet j
    calc
      _ ≤ 1 + ‖iteratedFDeriv ℝ (j + 1) f (G q)‖ :=
        flowJet_augmented_jet_norm_le hf (by omega) (G q)
      _ ≤ 2 + D j * W ^ (D j) * (1 + p (j + flowLoss + 1) z) := by linarith
      _ ≤ _ := stationaryInverse_weight_pack (hD j).le hW hs
  have hfull := hbound z hzI W hW N04FlowPoint N04FlowPoint F G q
    hF.contDiffAt hG.contDiffAt hfg J hJ hJbound hFbound n hn
  let π : N04FlowPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have he : (π : N04FlowPoint → ℝ) ∘ G = g := by
    funext y
    simp only [π, G, scalarFamilyLift, Function.comp_apply, ContinuousLinearMap.coe_snd']
  have hscalar := π.norm_iteratedFDeriv_comp_left (x := q) (n := n)
    hG.contDiffAt (by simp)
  rw [he] at hscalar
  exact (hscalar.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ) (norm_nonneg _))).trans hfull

end ContinuousFlexibility.Analysis
