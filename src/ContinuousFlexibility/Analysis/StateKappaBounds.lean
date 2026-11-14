module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Actual weighted bounds for the state control means

The level zero circle sum controls each circle's weighted `L²` norm.
The normalized angular mean is then bounded by Hölder's inequality in
the actual angular measure. The positive material weight is evaluated at
the same sample that occurs in `CircleMember`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem angleMeasure_univ_eq_pi : angleMeasure univ = ENNReal.ofReal Real.pi := by
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

/-- Hölder's inequality on the actual angular interval of length `π`. -/
theorem integral_abs_le_angleL2 {u : ℝ → ℝ} (hu : MemLp u 2 angleMeasure) :
    (∫ θ, |u θ| ∂angleMeasure) ≤ Real.sqrt Real.pi * (eLpNorm u 2 angleMeasure).toReal := by
  let : IsFiniteMeasure angleMeasure := ⟨by rw [angleMeasure_univ_eq_pi]; exact ENNReal.ofReal_lt_top⟩
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) angleMeasure := memLp_const 1
  have hu' : MemLp u (ENNReal.ofReal 2) angleMeasure := by simpa using hu
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hone hu'
  have hmass : (∫ _ : ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂angleMeasure) = Real.pi := by
    calc
      (∫ _ : ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂angleMeasure) = ∫ _ : ℝ, (1 : ℝ) ∂angleMeasure := by simp
      _ = (angleMeasure univ).toReal := by simp [integral_const, measureReal_def]
      _ = Real.pi := by rw [angleMeasure_univ_eq_pi, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hmass] at h
  have hnonneg : 0 ≤ ∫ θ, ‖u θ‖ ^ (2 : ℝ) ∂angleMeasure :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hnorm : (eLpNorm u 2 angleMeasure).toReal =
      (∫ θ, ‖u θ‖ ^ (2 : ℝ) ∂angleMeasure) ^ (1 / 2 : ℝ) := by
    rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [htwo, ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _), one_div]
  rw [hnorm, Real.sqrt_eq_rpow]
  simpa only [norm_one, one_mul, Real.norm_eq_abs] using h

theorem abs_angularMean_le_angleL2 {u : ℝ → ℝ} (hu : MemLp u 2 angleMeasure) :
    |angularMean u| ≤ ((1 / Real.pi) * Real.sqrt Real.pi) * (eLpNorm u 2 angleMeasure).toReal := by
  have hπ : 0 ≤ (1 : ℝ) / Real.pi := div_nonneg zero_le_one Real.pi_pos.le
  have hnorm : |∫ θ, u θ ∂angleMeasure| ≤ ∫ θ, |u θ| ∂angleMeasure := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := angleMeasure) u)
  unfold angularMean
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, abs_mul, abs_of_nonneg hπ]
  change (1 / Real.pi) * |∫ θ, u θ ∂angleMeasure| ≤ _
  calc
    _ ≤ (1 / Real.pi) * (∫ θ, |u θ| ∂angleMeasure) := mul_le_mul_of_nonneg_left hnorm hπ
    _ ≤ (1 / Real.pi) * (Real.sqrt Real.pi * (eLpNorm u 2 angleMeasure).toReal) :=
      mul_le_mul_of_nonneg_left (integral_abs_le_angleL2 hu) hπ
    _ = _ := (mul_assoc (1 / Real.pi) (Real.sqrt Real.pi) _).symm

/-- Extract the actual zero jet of a single circle from the level zero norm. -/
theorem circleMember_angleL2_le_weight {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hH : ∀ m, 0 < T.H (T.sample m)) (m : ℕ) :
    (eLpNorm (u m) 2 angleMeasure).toReal ≤ circleNorm T γ 0 u * T.H (T.sample m) ^ γ := by
  let term (i : ℕ) (j : CircleJetIndex 0) : ℝ≥0∞ :=
    ENNReal.ofReal ((T.M (T.sample i) ^ (j.val 1).val * T.H (T.sample i) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u i)) 2 angleMeasure ^ 2
  let total : ℝ≥0∞ := ∑' i : ℕ, ∑ j : CircleJetIndex 0, term i j
  have hfinite : total < ⊤ := hu.2.2 0
  have hsingle : term m (zeroCircleJetIndex 0) ≤ ∑ j : CircleJetIndex 0, term m j :=
    Finset.single_le_sum (f := term m) (fun _ _ => zero_le) (Finset.mem_univ _)
  have hsum : (∑ j : CircleJetIndex 0, term m j) ≤ total :=
    ENNReal.le_tsum (f := fun i => ∑ j : CircleJetIndex 0, term i j) m
  have hterm : ENNReal.ofReal ((T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (u m) 2 angleMeasure ^ 2 ≤ total := by
    simpa [term, zeroCircleJetIndex] using hsingle.trans hsum
  have hreal := ENNReal.toReal_mono hfinite.ne hterm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_pow] at hreal
  have hsq : (T.H (T.sample m) ^ (-γ) * (eLpNorm (u m) 2 angleMeasure).toReal) ^ 2 ≤
      total.toReal := by
    rw [mul_pow]
    exact hreal
  have hnonneg : 0 ≤ T.H (T.sample m) ^ (-γ) * (eLpNorm (u m) 2 angleMeasure).toReal :=
    mul_nonneg (Real.rpow_nonneg (hH m).le _) ENNReal.toReal_nonneg
  have hweighted := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnonneg] at hweighted
  change T.H (T.sample m) ^ (-γ) * (eLpNorm (u m) 2 angleMeasure).toReal ≤
    circleNorm T γ 0 u at hweighted
  rw [Real.rpow_neg (hH m).le, ← div_eq_inv_mul] at hweighted
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (hH m) γ)).mp hweighted

/-- The decoded circle mean obeys the sample weight with a uniform constant. -/
theorem circleMember_angularMean_bound {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hH : ∀ m, 0 < T.H (T.sample m)) (m : ℕ) :
    |angularMean (u m)| ≤
      (((1 / Real.pi) * Real.sqrt Real.pi) * circleNorm T γ 0 u) * T.H (T.sample m) ^ γ := by
  have hm : MemLp (u m) 2 angleMeasure := by simpa using hu.2.1 m 0
  have hconst : 0 ≤ (1 / Real.pi) * Real.sqrt Real.pi :=
    mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (Real.sqrt_nonneg _)
  calc
    |angularMean (u m)| ≤ ((1 / Real.pi) * Real.sqrt Real.pi) * (eLpNorm (u m) 2 angleMeasure).toReal :=
      abs_angularMean_le_angleL2 hm
    _ ≤ ((1 / Real.pi) * Real.sqrt Real.pi) * (circleNorm T γ 0 u * T.H (T.sample m) ^ γ) :=
      mul_le_mul_of_nonneg_left (circleMember_angleL2_le_weight hu hH m) hconst
    _ = _ := (mul_assoc ((1 / Real.pi) * Real.sqrt Real.pi) (circleNorm T γ 0 u) _).symm

theorem materialSample_mem_radialCore {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (m : ℕ) :
    T.sample m ∈ radialCore D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩ := hT
  exact hPart.2.2.2.1 m (hsample m)

theorem stateKappa_weight_bound {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b) (x : AnnularState S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m, |stateKappa S x m| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  let u := (S.circle (3 / 4 : ℝ)).decode x.2.2.1
  have hu : CircleMember T (3 / 4 : ℝ) u := (hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  let K := ((1 / Real.pi) * Real.sqrt Real.pi) * circleNorm T (3 / 4 : ℝ) 0 u
  refine ⟨K, ?_, fun m => circleMember_angularMean_bound hu hH m⟩
  exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem stateKappa_weight_bound_of_accumulatingProfile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (x : AnnularState S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m, |stateKappa S x m| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  obtain ⟨_, hbounds⟩ := hRef
  exact stateKappa_weight_bound hS hT (materialSample_mem_radialCore hT hbounds.2.1) x

end ContinuousFlexibility.Statements
