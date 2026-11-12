import ContinuousFlexibility.Analysis.InteriorFlowTransport
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
import ContinuousFlexibility.Analysis.FlowJetLinearization
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual spatial jets of an interior endpoint map

The normalized radial endpoint parameter is affine. Pulling the actual
flow displacement back by this map preserves its derivative loss; only
the fixed affine norm enters the numerical constants. Positive jets of
the full angular lift are then recovered by adding the linear angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A linear coordinate contributes only its operator norm to a positive
ordinary jet. This also applies to displacements on higher-dimensional
parameter spaces. -/
theorem norm_positiveJet_le_linear_displacement
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] ℝ)
    {n : ℕ} (hn : 1 ≤ n) (x : X) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      ‖iteratedFDeriv ℝ n (fun y : X => f y - L y) x‖ + ‖L‖ := by
  have he : iteratedFDeriv ℝ n (fun y : X => f y - L y) x =
      iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n (L : X → ℝ) x :=
    iteratedFDeriv_sub_apply
      (hf.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) L.contDiff.contDiffAt
  calc
    _ = ‖(iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n (L : X → ℝ) x) +
        iteratedFDeriv ℝ n (L : X → ℝ) x‖ := by rw [sub_add_cancel]
    _ ≤ ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n (L : X → ℝ) x‖ +
        ‖iteratedFDeriv ℝ n (L : X → ℝ) x‖ := norm_add_le _ _
    _ ≤ _ := by rw [← he]; exact add_le_add le_rfl (flowJet_norm_iteratedFDeriv_clm_le L hn x)

def interiorEndpointPullback
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (a b : ℝ) (q : PolarPoint) : ℝ :=
  Θ (interiorEndpointParameter a b q.1) 1 q.2

private def interiorEndpointLinear (a b : ℝ) : PolarPoint →L[ℝ] N04FlowPoint :=
  (((2 / (b - a)) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (0 : PolarPoint →L[ℝ] ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private def interiorEndpointOffset (a b : ℝ) : N04FlowPoint :=
  ((-(2 * a) / (b - a) - 1, 0), 0)

private theorem interiorEndpoint_affine (a b : ℝ) (q : PolarPoint) :
    interiorEndpointOffset a b + interiorEndpointLinear a b q =
      (interiorEndpointParameter a b q.1, q.2) := by
  ext <;> simp only [interiorEndpointOffset, interiorEndpointLinear,
    interiorEndpointParameter, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.zero_apply,
    Prod.mk_add_mk, smul_eq_mul, add_zero, zero_add] <;> ring

theorem contDiff_interiorEndpointPullback
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : ContDiff ℝ ∞ (fun q : N04FlowPoint => Θ q.1 1 q.2)) (a b : ℝ) :
    ContDiff ℝ ∞ (interiorEndpointPullback Θ a b) := by
  have hmap : ContDiff ℝ ∞ (fun x : PolarPoint =>
      interiorEndpointOffset a b + interiorEndpointLinear a b x) :=
    contDiff_const.add (interiorEndpointLinear a b).contDiff
  have h := hΘ.comp hmap
  have he : (fun q : N04FlowPoint => Θ q.1 1 q.2) ∘
      (fun x : PolarPoint => interiorEndpointOffset a b + interiorEndpointLinear a b x) =
      interiorEndpointPullback Θ a b := by
    funext x
    rw [Function.comp_apply, interiorEndpoint_affine]
    rfl
  rw [he] at h
  exact h

theorem exists_interiorEndpoint_displacement_jet_constants
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) {a b : ℝ} (hab : a < b) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, ∀ Λ : ℝ, ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowJetBounds p loss A z 1 Λ Θ →
      ∀ q : PolarPoint, q.1 ∈ Icc a b →
        PointwiseMaterialJetBound p loss B z
          (fun x => interiorEndpointPullback Θ a b x - x.2) q := by
  let M := interiorEndpointLinear a b
  let c := interiorEndpointOffset a b
  let B : ℕ → ℝ := fun n => (1 + ‖M‖ ^ n) * A n
  have hB (n : ℕ) : 0 < B n :=
    mul_pos (add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg (norm_nonneg M) n)) (hA n)
  refine ⟨B, hB, ?_⟩
  intro z Λ Θ hΘ q hq
  let f : N04FlowPoint → ℝ := fun y => Θ y.1 1 y.2 - y.2
  have hf : ContDiff ℝ ∞ f := (hΘ 1 ⟨zero_le_one, le_rfl⟩).1.sub contDiff_snd
  have hb : PointwiseMaterialJetBound p loss A z f (c + M q) := by
    intro n
    rw [show c + M q = (interiorEndpointParameter a b q.1, q.2) from
      interiorEndpoint_affine a b q]
    simpa only [Real.one_rpow, mul_one] using
      (hΘ 1 ⟨zero_le_one, le_rfl⟩).2.2.2 n
        (interiorEndpointParameter a b q.1, q.2) (interiorEndpointParameter_mem hab hq)
  have ha := PointwiseMaterialJetBound.affine_comp M c hf.contDiffAt hb
  have he : (fun x => f (c + M x)) =
      (fun x => interiorEndpointPullback Θ a b x - x.2) := by
    funext x
    rw [show c + M x = (interiorEndpointParameter a b x.1, x.2) from
      interiorEndpoint_affine a b x]
    rfl
  rw [he] at ha
  intro n
  exact (ha n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (hA n).le)
      (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
