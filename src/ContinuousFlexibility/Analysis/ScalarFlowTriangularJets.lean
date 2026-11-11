import ContinuousFlexibility.Analysis.FlowJetLinearization
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Triangular mixed jets of an augmented scalar flow

The external parameters of the augmented map remain fixed. Its
linearized scalar field therefore acts on the highest flow jet only
through the angular derivative. All remaining terms involve lower
flow jets and original field jets, with their exact partition orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The part of a scalar linear functional acting on the external
parameter, viewed on the full parameter-angle space. -/
def flowJet_parameterLinearPart (L : (P × ℝ) →L[ℝ] ℝ) :
    (P × ℝ) →L[ℝ] ℝ :=
  (L.comp (ContinuousLinearMap.inl ℝ P ℝ)).comp
    (ContinuousLinearMap.fst ℝ P ℝ)

theorem flowJet_parameterLinearPart_apply (L : (P × ℝ) →L[ℝ] ℝ) (x : P × ℝ) :
    flowJet_parameterLinearPart L x = L (x.1, 0) := by
  simp only [flowJet_parameterLinearPart, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply]

theorem flowJet_parameterLinearPart_norm_le (L : (P × ℝ) →L[ℝ] ℝ) :
    ‖flowJet_parameterLinearPart L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  rw [flowJet_parameterLinearPart_apply]
  have hx : ‖(x.1, (0 : ℝ))‖ ≤ ‖x‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x.1)]
    exact norm_fst_le x
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg L))

theorem flowJet_linear_augmented_eq (L : (P × ℝ) →L[ℝ] ℝ)
    (h : P × ℝ → ℝ) :
    (L : P × ℝ → ℝ) ∘ (fun y : P × ℝ => (y.1, h y)) =
      (flowJet_parameterLinearPart L : P × ℝ → ℝ) + L (0, 1) • h := by
  funext y
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    flowJet_parameterLinearPart_apply]
  have hz : L (0, h y) = h y * L (0, 1) := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using
      L.map_smul (h y) ((0, 1) : P × ℝ)
  calc
    L (y.1, h y) = L (y.1, 0) + L (0, h y) := by
      rw [← L.map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    _ = _ := by rw [hz, mul_comm (h y)]

theorem flowJet_linear_augmented_jet (L : (P × ℝ) →L[ℝ] ℝ)
    {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (n : ℕ) (x : P × ℝ) :
    iteratedFDeriv ℝ n
        ((L : P × ℝ → ℝ) ∘ (fun y : P × ℝ => (y.1, h y))) x =
      iteratedFDeriv ℝ n (flowJet_parameterLinearPart L : P × ℝ → ℝ) x +
        L (0, 1) • iteratedFDeriv ℝ n h x := by
  have hs : ContDiffAt ℝ n (L (0, 1) • h) x := by
    have he : (fun y : P × ℝ => L (0, 1) • h y) = L (0, 1) • h := by
      funext y
      exact (Pi.smul_apply _ _ y).symm
    rw [← he]
    exact (hh.const_smul (L (0, 1))).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [flowJet_linear_augmented_eq, iteratedFDeriv_add_apply
    (flowJet_parameterLinearPart L).contDiff.contDiffAt
    hs,
    iteratedFDeriv_const_smul_apply
      (hh.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]

theorem flowJet_angular_deriv_eq_fderiv
    {g : P × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (x : P × ℝ) :
    deriv (fun θ : ℝ => g (x.1, θ)) x.2 = fderiv ℝ g x (0, 1) := by
  have hcurve : HasDerivAt (fun θ : ℝ => (x.1, θ)) (0, 1) x.2 := by
    simpa only [id_eq] using
      HasDerivAt.prodMk (hasDerivAt_const (x := x.2) (c := x.1))
        (hasDerivAt_id x.2)
  have hd := (hg.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt x.2 hcurve
  have he : g ∘ (fun θ : ℝ => (x.1, θ)) = (fun θ => g (x.1, θ)) := by
    funext θ
    exact Function.comp_apply
  rw [he] at hd
  exact hd.deriv

/-- The fixed parameter component contributes at most one to a
positive-order jet of the augmented map. -/
theorem flowJet_augmented_jet_norm_le {h : P × ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {n : ℕ} (hn : 1 ≤ n) (x : P × ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : P × ℝ => (y.1, h y)) x‖ ≤
      1 + ‖iteratedFDeriv ℝ n h x‖ := by
  rw [iteratedFDeriv_prodMk contDiffAt_fst
    (hh.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  have hf : ‖iteratedFDeriv ℝ n (fun y : P × ℝ => y.1) x‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.coe_fst'] using
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.fst ℝ P ℝ) hn x).trans
        (ContinuousLinearMap.norm_fst_le ℝ P ℝ)
  exact max_le (hf.trans (le_add_of_nonneg_right (norm_nonneg _)))
    (le_add_of_nonneg_left zero_le_one)

/-- The first mixed spatial jet has a separate forcing term from the
external parameter. Its coefficient on the flow derivative is angular. -/
theorem flowJet_augmented_comp_first_norm_le
    {g h : P × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (x : P × ℝ) :
    ‖iteratedFDeriv ℝ 1 (g ∘ (fun y : P × ℝ => (y.1, h y))) x‖ ≤
      ‖iteratedFDeriv ℝ 1 g (x.1, h x)‖ +
        |deriv (fun θ => g (x.1, θ)) (h x)| * ‖iteratedFDeriv ℝ 1 h x‖ := by
  let H : P × ℝ → P × ℝ := fun y => (y.1, h y)
  let L : (P × ℝ) →L[ℝ] ℝ := fderiv ℝ g (H x)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk hh
  have hd : fderiv ℝ (g ∘ H) x = fderiv ℝ ((L : P × ℝ → ℝ) ∘ H) x := by
    rw [fderiv_comp x (hg.differentiable (by simp) (H x))
      (hH.differentiable (by simp) x),
      fderiv_comp x L.differentiableAt (hH.differentiable (by simp) x), L.fderiv]
  have ha : L (0, 1) = deriv (fun θ => g (x.1, θ)) (h x) :=
    (flowJet_angular_deriv_eq_fderiv hg (x.1, h x)).symm
  have he : ‖iteratedFDeriv ℝ 1 (g ∘ H) x‖ =
      ‖iteratedFDeriv ℝ 1 ((L : P × ℝ → ℝ) ∘ H) x‖ := by
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, hd]
  change ‖iteratedFDeriv ℝ 1 (g ∘ H) x‖ ≤ _
  rw [he, flowJet_linear_augmented_jet L hh, norm_iteratedFDeriv_one g]
  calc
    _ ≤ ‖iteratedFDeriv ℝ 1 (flowJet_parameterLinearPart L : P × ℝ → ℝ) x‖ +
        ‖L (0, 1) • iteratedFDeriv ℝ 1 h x‖ := norm_add_le _ _
    _ ≤ ‖L‖ + |deriv (fun θ => g (x.1, θ)) (h x)| *
        ‖iteratedFDeriv ℝ 1 h x‖ := by
      rw [norm_iteratedFDeriv_one, (flowJet_parameterLinearPart L).fderiv,
        norm_smul, Real.norm_eq_abs, ha]
      exact add_le_add (flowJet_parameterLinearPart_norm_le L) le_rfl
    _ = _ := rfl

/-- At every higher order, only the actual angular derivative multiplies
the highest flow jet. All other terms use strictly lower inner jets. -/
theorem flowJet_augmented_comp_high_norm_le
    {g h : P × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {n : ℕ} (hn : 2 ≤ n) (x : P × ℝ) :
    ‖iteratedFDeriv ℝ n (g ∘ (fun y : P × ℝ => (y.1, h y))) x‖ ≤
      |deriv (fun θ => g (x.1, θ)) (h x)| * ‖iteratedFDeriv ℝ n h x‖ +
      ∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          ‖iteratedFDeriv ℝ c.length g (x.1, h x)‖ *
            ∏ j, (1 + ‖iteratedFDeriv ℝ (c.partSize j) h x‖)
        else 0 := by
  classical
  let H : P × ℝ → P × ℝ := fun y => (y.1, h y)
  let L : (P × ℝ) →L[ℝ] ℝ := fderiv ℝ g (H x)
  let R : P × ℝ → ℝ := g - (L : P × ℝ → ℝ)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk hh
  have hR : ContDiff ℝ ∞ R := hg.sub L.contDiff
  have he : g ∘ H = (R ∘ H) + ((L : P × ℝ → ℝ) ∘ H) := by
    funext y
    exact (sub_add_cancel (g (H y)) (L (H y))).symm
  have hlinear :
      ‖iteratedFDeriv ℝ n ((L : P × ℝ → ℝ) ∘ H) x‖ =
        |deriv (fun θ => g (x.1, θ)) (h x)| * ‖iteratedFDeriv ℝ n h x‖ := by
    rw [flowJet_linear_augmented_jet L hh,
      flowJet_iteratedFDeriv_clm_eq_zero (flowJet_parameterLinearPart L) hn,
      zero_add, norm_smul, Real.norm_eq_abs]
    rw [flowJet_angular_deriv_eq_fderiv hg (x.1, h x)]
  have hnonlinear :
      ‖iteratedFDeriv ℝ n (R ∘ H) x‖ ≤
        ∑ c : OrderedFinpartition n,
          if 2 ≤ c.length then
            ‖iteratedFDeriv ℝ c.length g (x.1, h x)‖ *
              ∏ j, (1 + ‖iteratedFDeriv ℝ (c.partSize j) h x‖)
          else 0 := by
    apply (flowJet_linearization_remainder_bound hg hH (by omega : 0 < n) x).trans
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : 2 ≤ c.length
    · rw [if_pos hc, if_pos hc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => flowJet_augmented_jet_norm_le hh (c.partSize_pos j) x)
    · rw [if_neg hc, if_neg hc]
  change ‖iteratedFDeriv ℝ n (g ∘ H) x‖ ≤ _
  rw [he, iteratedFDeriv_add_apply
    ((hR.comp hH).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    ((L.contDiff.comp hH).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (R ∘ H) x‖ +
        ‖iteratedFDeriv ℝ n ((L : P × ℝ → ℝ) ∘ H) x‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [hlinear, add_comm]
      exact add_le_add le_rfl hnonlinear

end ContinuousFlexibility.Analysis
