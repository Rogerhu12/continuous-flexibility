module

public import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialFlowPrefix
public import ContinuousFlexibility.Analysis.WeightedJetComposition
public import ContinuousFlexibility.Analysis.N07bFiniteJetAlgebra

/-!
# Spatial powers for the actual linearization along a root flow

Positive flow jets of order j carry spatial weight j-1. In composition
with a field whose order j jet carries weight j, these powers add to
exactly the requested output order. The angular linearization is the
actual directional derivative of the original field along its actual
flow, so no bound for a candidate linear coefficient is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The output amplitude is linear, while the inner jet envelope costs
only an ordinary finite power. Derivative orders determine the spatial
power before the numerical bounds are combined. -/
theorem n04NegativeGeometry_weighted_composition_jet_le
    {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : X → Y} {g : Y → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : X) (n : ℕ) {A B ρ : ℝ} (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A * ρ ^ j)
    (hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B * ρ ^ (j - 1)) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * A * B ^ n * ρ ^ n := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have ho (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ (A * ρ ^ n) * (ρ⁻¹) ^ (n - j) := by
    have hp : ρ ^ n = ρ ^ j * ρ ^ (n - j) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    have he : (A * ρ ^ n) * (ρ⁻¹) ^ (n - j) = A * ρ ^ j := by
      rw [hp, inv_pow]
      field_simp [hρpos.ne']
      <;> ring
    rw [he]
    exact houter j hj
  have hi (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ ρ⁻¹ * (B / ρ⁻¹) ^ j := by
    have hp : ρ ^ j = ρ ^ (j - 1) * ρ := by
      rw [← pow_succ, Nat.sub_add_cancel hj]
    have he : ρ⁻¹ * (B / ρ⁻¹) ^ j = B ^ j * ρ ^ (j - 1) := by
      rw [div_inv_eq_mul, mul_pow, hp]
      field_simp [hρpos.ne']
      <;> ring
    rw [he]
    exact (hinner j hj hjn).trans (mul_le_mul_of_nonneg_right
      (by simpa only [pow_one] using pow_le_pow_right₀ hB hj)
      (pow_nonneg hρpos.le _))
  have hb := norm_iteratedFDeriv_comp_le_weighted isOpen_univ hf.contDiffOn hg
    (mem_univ x) (inv_pos.mpr hρpos) n ho hi
  exact hb.trans_eq (by ring)

private theorem field_angle_eq_fderiv
    {F : ℝ × N04FlowPoint → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ)
    (q : N04FlowPoint) :
    deriv (fun θ : ℝ => F (t, (q.1, θ))) q.2 =
      fderiv ℝ (fun y : N04FlowPoint => F (t, y)) q ((0, 0), 1) := by
  have hs : ContDiff ℝ ∞ (fun y : N04FlowPoint => F (t, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hd := (hs.differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  simpa only [Function.comp_def, id_eq, Prod.zero_eq_mk] using hd.deriv

theorem n04NegativeGeometry_field_angle_contDiff
    {F : ℝ × N04FlowPoint → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun q : N04FlowPoint =>
      deriv (fun θ : ℝ => F (t, (q.1, θ))) q.2) := by
  have hs : ContDiff ℝ ∞ (fun y : N04FlowPoint => F (t, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun q : N04FlowPoint => deriv (fun θ : ℝ => F (t, (q.1, θ))) q.2) =
      fun q : N04FlowPoint => fderiv ℝ (fun y : N04FlowPoint => F (t, y)) q ((0, 0), 1) :=
    funext (field_angle_eq_fderiv hF t)
  rw [he]
  exact (hs.fderiv_right (by simp)).clm_apply contDiff_const

theorem n04NegativeGeometry_field_angle_jet_le
    {F : ℝ × N04FlowPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (q : N04FlowPoint) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun p : N04FlowPoint =>
      deriv (fun θ : ℝ => F (t, (p.1, θ))) p.2) q‖ ≤
        ‖iteratedFDeriv ℝ (j + 1) (fun p : N04FlowPoint => F (t, p)) q‖ := by
  have hs : ContDiff ℝ ∞ (fun y : N04FlowPoint => F (t, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun p : N04FlowPoint => deriv (fun θ : ℝ => F (t, (p.1, θ))) p.2) =
      fun p : N04FlowPoint => fderiv ℝ (fun y : N04FlowPoint => F (t, y)) p ((0, 0), 1) :=
    funext (field_angle_eq_fderiv hF t)
  rw [he]
  have hb := n07b_norm_jet_directional_le isOpen_univ hs.contDiffOn
    (mem_univ q) j (((0, 0), 1) : N04FlowPoint)
  simpa only [Prod.norm_def, norm_zero, norm_one, max_self, max_eq_right zero_le_one,
    one_mul] using hb

/-- All spatial jets of the genuine angular linearization have one
common geometric scale. Its zeroth integral smallness is supplied by
the original angular-control hypothesis, separately from this polynomial
bound on positive derivatives. -/
theorem n04NegativeGeometry_flowCoefficient_weighted_prefix (Λ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {A ρ : ℝ}, 1 ≤ A → 1 ≤ ρ →
      ∀ (F : ℝ × N04FlowPoint → ℝ), ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ M : ℕ → ℝ, (∀ j, 0 ≤ M j) → N04FlowPositiveRawBounds M F →
      N04FlowAngularControl F Λ →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint,
        q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (t, y)) q‖ ≤ A * ρ ^ j) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ k (fun y : N04FlowPoint =>
          deriv (fun θ : ℝ => F (t, (y.1, θ))) (Θ y.1 t y.2)) q‖ ≤
            C * A ^ e * ρ ^ k := by
  obtain ⟨C, e, hC, hflow⟩ := n04NegativeGeometry_flow_spatial_weighted_prefix Λ N
  refine ⟨(N.factorial : ℝ) * C ^ N, e * N + 1,
    one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos N)) (one_le_pow₀ hC), ?_⟩
  intro A ρ hA hρ F hF hperiod M hM hraw hangular hprefix Θ hΘ k hk t ht q hq
  let B : ℝ := C * A ^ e
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hA)
  have hΘt : ContDiff ℝ ∞ (fun y : N04FlowPoint => Θ y.1 t y.2) :=
    n04Flow_contDiff_slice hF hperiod hΘ ht
  let Ψ : N04FlowPoint → N04FlowPoint := fun y => (y.1, Θ y.1 t y.2)
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_fst.prodMk hΘt
  have hinner (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
      ‖iteratedFDeriv ℝ j Ψ q‖ ≤ B * ρ ^ (j - 1) := by
    have hflowj := hflow hA hρ F hF hperiod M hM hraw hangular hprefix Θ hΘ
      (j - 1) (by omega) t ht q hq
    rw [Nat.sub_add_cancel hj] at hflowj
    have hproj : ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => y.1) q‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.coe_fst'] using
        (flowJet_norm_iteratedFDeriv_clm_le
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) hj q).trans
          (ContinuousLinearMap.norm_fst_le ℝ (ℝ × ℝ) ℝ)
    change ‖iteratedFDeriv ℝ j
      (fun y : N04FlowPoint => (y.1, Θ y.1 t y.2)) q‖ ≤ _
    rw [iteratedFDeriv_prodMk contDiffAt_fst hΘt.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le (hproj.trans
      (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hρ))) hflowj
  have houter (j : ℕ) (hjk : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        deriv (fun θ : ℝ => F (t, (y.1, θ))) y.2) (Ψ q)‖ ≤ A * ρ ^ j :=
    (n04NegativeGeometry_field_angle_jet_le hF t (Ψ q) j).trans
      (hprefix j (hjk.trans hk) t ht (Ψ q) hq)
  have hb := n04NegativeGeometry_weighted_composition_jet_le hΨ
    (n04NegativeGeometry_field_angle_contDiff hF t) q k hB hρ houter hinner
  have hfac : (k.factorial : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hk
  calc
    _ ≤ (k.factorial : ℝ) * A * B ^ k * ρ ^ k := hb
    _ ≤ (N.factorial : ℝ) * A * B ^ N * ρ ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hfac (zero_le_one.trans hA))
          (pow_le_pow_right₀ hB hk) (pow_nonneg (zero_le_one.trans hB) _)
          (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hA)))
        (pow_nonneg (zero_le_one.trans hρ) _)
    _ = ((N.factorial : ℝ) * C ^ N) * A ^ (e * N + 1) * ρ ^ k := by
      dsimp only [B]
      rw [mul_pow, ← pow_mul, pow_succ]
      ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_flowCoefficient_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_flowCoefficient_weighted_prefix
