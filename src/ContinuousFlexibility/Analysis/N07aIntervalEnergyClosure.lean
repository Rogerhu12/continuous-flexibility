import ContinuousFlexibility.Analysis.N07aIntervalH2Density
import ContinuousFlexibility.Analysis.N06DegenerateGraph
import ContinuousFlexibility.Analysis.L2BoundedMultiplier

/-!
# The positive-cylinder estimate on the actual weak H² graph

The smooth estimate is applied to the genuine graph approximants produced
by two integrations. Every energy term is a continuous quadratic form on
the actual L² class, so the same frequency-uniform estimate passes to the
weak graph. No endpoint condition is imposed on the original solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

/-- Actual multiplication by a coefficient continuous on the closed unit
interval. The compact bound is used solely to construct the linear map. -/
def n07aIntervalC0Mul (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1)) :
    N07aIntervalL2 →L[ℝ] N07aIntervalL2 := by
  let h := isCompact_Icc.bddAbove_image ha.norm
  let C := h.choose
  have hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖a x‖ ≤ C :=
    fun x hx => h.choose_spec ⟨x, hx, rfl⟩
  apply l2BoundedMultiplier (volume.restrict (Ioo (0 : ℝ) 1))
    ((ha.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x (Ioo_subset_Icc_self hx)

theorem n07aIntervalC0Mul_ae (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (u : N07aIntervalL2) :
    (n07aIntervalC0Mul a ha u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => a x * u x) := by
  unfold n07aIntervalC0Mul
  exact l2BoundedMultiplier_ae _ _ _ _

/-- The bounded multiplication quadratic form is the actual weighted
square integral. -/
theorem n07aIntervalC0Mul_inner (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (u : N07aIntervalL2) :
    inner ℝ u (n07aIntervalC0Mul a ha u) = ∫ x in Ioo (0 : ℝ) 1, a x * u x ^ 2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [n07aIntervalC0Mul_ae a ha u] with x hx
  rw [hx, Real.inner_apply]
  ring

/-- A power of the geometric cylinder weight acting on the actual class. -/
def n07aCylinderPower (p : ℕ) : N07aIntervalL2 →L[ℝ] N07aIntervalL2 :=
  n07aIntervalC0Mul (fun x => cylinderWeight x ^ p)
    (cylinderWeight_continuous.pow p).continuousOn

def n07aCylinderSquare (p : ℕ) (u : N07aIntervalL2) : ℝ :=
  inner ℝ u (n07aCylinderPower p u)

theorem n07aCylinderSquare_eq (p : ℕ) (u : N07aIntervalL2) :
    n07aCylinderSquare p u = ∫ x in Ioo (0 : ℝ) 1, cylinderWeight x ^ p * u x ^ 2 :=
  n07aIntervalC0Mul_inner _ _ u

theorem n07aCylinderSquare_continuous (p : ℕ) : Continuous (n07aCylinderSquare p) :=
  continuous_id.inner (n07aCylinderPower p).continuous

def n07aCylinderEnergy (j : ℝ) (u d dd : N07aIntervalL2) : ℝ :=
  n07aCylinderSquare 2 d + (1 + j ^ 2) * n07aCylinderSquare 3 u +
    n07aCylinderSquare 4 dd + (1 + j ^ 2) ^ 2 * n07aCylinderSquare 6 u +
    (1 + j ^ 2) * n07aCylinderSquare 5 d

/-- The actual L² scalar differential expression determined by its three
weak derivative coordinates. -/
def n07aIntervalDifferential (a c V : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (hc : Continuous c) (hV : Continuous V) (j : ℝ)
    (u d dd : N07aIntervalL2) : N07aIntervalL2 :=
  -(n07aIntervalC0Mul a ha.continuous.continuousOn dd) -
    n07aIntervalC0Mul (deriv a) (ha.continuous_deriv le_rfl).continuousOn d +
    j ^ 2 • n07aIntervalC0Mul c hc.continuousOn u +
    n07aIntervalC0Mul V hV.continuousOn u

theorem n07aIntervalDifferential_ae (a c V : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (hc : Continuous c) (hV : Continuous V) (j : ℝ)
    (u d dd : N07aIntervalL2) :
    (n07aIntervalDifferential a c V ha hc hV j u d dd : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => -a x * dd x - deriv a x * d x + j ^ 2 * c x * u x + V x * u x) := by
  let Ma := n07aIntervalC0Mul a ha.continuous.continuousOn
  let Md := n07aIntervalC0Mul (deriv a) (ha.continuous_deriv le_rfl).continuousOn
  let Mc := n07aIntervalC0Mul c hc.continuousOn
  let Mv := n07aIntervalC0Mul V hV.continuousOn
  filter_upwards [Lp.coeFn_add (-Ma dd - Md d + j ^ 2 • Mc u) (Mv u),
    Lp.coeFn_add (-Ma dd - Md d) (j ^ 2 • Mc u), Lp.coeFn_sub (-Ma dd) (Md d),
    Lp.coeFn_neg (Ma dd), Lp.coeFn_smul (j ^ 2) (Mc u),
    n07aIntervalC0Mul_ae a ha.continuous.continuousOn dd,
    n07aIntervalC0Mul_ae (deriv a) (ha.continuous_deriv le_rfl).continuousOn d,
    n07aIntervalC0Mul_ae c hc.continuousOn u,
    n07aIntervalC0Mul_ae V hV.continuousOn u] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h₁ h₂ h₃ h₄ h₅
  change (-Ma dd - Md d + j ^ 2 • Mc u + Mv u) x = _
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
  ring

private theorem n07a_interval_sq_of_ae {u : N07aIntervalL2} {f : ℝ → ℝ}
    (hf : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) :
    ‖u‖ ^ 2 = ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  have h := norm_toLp_sq_eq_integral_sq (Lp.memLp u)
  rw [Lp.toLp_coeFn] at h
  rw [h, intervalIntegral.integral_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_congr_ae (hf.mono fun _ h => congrArg (· ^ 2) h)

private theorem n07a_cylinderSquare_of_ae (p : ℕ) {u : N07aIntervalL2} {f : ℝ → ℝ}
    (hf : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) :
    n07aCylinderSquare p u = ∫ x in (0 : ℝ)..1, cylinderWeight x ^ p * f x ^ 2 := by
  rw [n07aCylinderSquare_eq, intervalIntegral.integral_of_le zero_le_one,
    ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_congr_ae (hf.mono fun x h =>
    congrArg (fun t => cylinderWeight x ^ p * t ^ 2) h)

/-- The original smooth cubic estimate now holds on the maximal actual
second weak derivative graph, with its unchanged uniform frequency factor. -/
theorem n07a_weak_cubic_graph_bound {a c V q : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V)
    (hq : ContDiff ℝ 2 q) (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K)
    (u d dd : N07aIntervalL2)
    (hud : HasIntervalWeakDerivative 0 1 u d)
    (hdd : HasIntervalWeakDerivative 0 1 d dd) :
    n07aCylinderEnergy j u d dd ≤ 16384 * K ^ 10 *
      (‖n07aIntervalDifferential a c V ha hc hV j u d dd‖ ^ 2 + ‖u‖ ^ 2) := by
  obtain ⟨f, f₀, f₁, f₂, hf, ht₀, ht₁, ht₂⟩ :=
    n07a_intervalH2_smooth_approximation u d dd hud hdd
  have hbound (n : ℕ) : n07aCylinderEnergy j (f₀ n) (f₁ n) (f₂ n) ≤
      16384 * K ^ 10 *
        (‖n07aIntervalDifferential a c V ha hc hV j (f₀ n) (f₁ n) (f₂ n)‖ ^ 2 +
          ‖f₀ n‖ ^ 2) := by
    let F : ℝ → ℝ := fun y => -deriv (fun t => a t * deriv (f n) t) y +
      j ^ 2 * c y * f n y + V y * f n y
    have hFa : (n07aIntervalDifferential a c V ha hc hV j (f₀ n) (f₁ n) (f₂ n) : ℝ → ℝ)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] F := by
      filter_upwards [n07aIntervalDifferential_ae a c V ha hc hV j (f₀ n) (f₁ n) (f₂ n),
        (hf n).2.1, (hf n).2.2.1, (hf n).2.2.2] with x hx h₀ h₁ h₂
      rw [hx, h₀, h₁, h₂]
      have hd := ((ha.differentiable (by norm_num) x).hasDerivAt).fun_mul
        (((contDiff_infty_iff_deriv.mp (hf n).1).2.differentiable (by simp) x).hasDerivAt)
      dsimp only [F]
      rw [hd.deriv]
      ring
    have h := n06_smooth_cubic_graph_bound ha ((hf n).1.of_le (by simp)) hc hV hq
      (F := F) (fun _ => rfl) hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
    rw [n07a_interval_sq_of_ae hFa, n07a_interval_sq_of_ae (hf n).2.1]
    unfold n07aCylinderEnergy
    rw [n07a_cylinderSquare_of_ae 2 (hf n).2.2.1,
      n07a_cylinderSquare_of_ae 3 (hf n).2.1,
      n07a_cylinderSquare_of_ae 4 (hf n).2.2.2,
      n07a_cylinderSquare_of_ae 6 (hf n).2.1,
      n07a_cylinderSquare_of_ae 5 (hf n).2.2.1]
    simpa only [mul_pow, ← pow_mul, Nat.reduceMul] using h
  have hleft : Tendsto (fun n => n07aCylinderEnergy j (f₀ n) (f₁ n) (f₂ n)) atTop
      (𝓝 (n07aCylinderEnergy j u d dd)) := by
    unfold n07aCylinderEnergy
    exact (((((n07aCylinderSquare_continuous 2).tendsto _).comp ht₁).add
      ((((n07aCylinderSquare_continuous 3).tendsto _).comp ht₀).const_mul _)).add
      (((n07aCylinderSquare_continuous 4).tendsto _).comp ht₂)).add
      ((((n07aCylinderSquare_continuous 6).tendsto _).comp ht₀).const_mul _) |>.add
      ((((n07aCylinderSquare_continuous 5).tendsto _).comp ht₁).const_mul _)
  have hF : Tendsto (fun n => n07aIntervalDifferential a c V ha hc hV j
      (f₀ n) (f₁ n) (f₂ n)) atTop
      (𝓝 (n07aIntervalDifferential a c V ha hc hV j u d dd)) := by
    unfold n07aIntervalDifferential
    exact (((((n07aIntervalC0Mul a ha.continuous.continuousOn).continuous.tendsto _).comp ht₂).neg.sub
      (((n07aIntervalC0Mul (deriv a) (ha.continuous_deriv le_rfl).continuousOn).continuous.tendsto _).comp ht₁)).add
      ((((n07aIntervalC0Mul c hc.continuousOn).continuous.tendsto _).comp ht₀).const_smul (j ^ 2))).add
      (((n07aIntervalC0Mul V hV.continuousOn).continuous.tendsto _).comp ht₀)
  exact le_of_tendsto_of_tendsto hleft
    (((hF.norm.pow 2).add (ht₀.norm.pow 2)).const_mul (16384 * K ^ 10))
    (Eventually.of_forall hbound)

end ContinuousFlexibility.Analysis
