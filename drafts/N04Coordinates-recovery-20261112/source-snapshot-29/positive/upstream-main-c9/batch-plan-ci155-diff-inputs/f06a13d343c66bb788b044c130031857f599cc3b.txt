import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.OrderClosed

/-!
# Quantitative division by the distance to an optical root

The quotient is the actual integral of the first derivative. Its Lipschitz
bound uses the second derivative of the original function, including at the
root. The last two lemmas locate an equal-travel cut and convert a lower
bound using both roots into a lower bound using either root distance.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The continuous extension of `F x / x` when `F 0 = 0`. -/
def n05OpticalRootQuotient (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv F (t * x)

theorem n05_optical_unit_mul_mem {a x t : ℝ}
    (hx : x ∈ Icc (0 : ℝ) a) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x ∈ Icc (0 : ℝ) a := by
  exact ⟨mul_nonneg ht.1 hx.1,
    (mul_le_mul_of_nonneg_right ht.2 hx.1).trans (by simpa using hx.2)⟩

theorem n05_optical_deriv_continuousOn {F : ℝ → ℝ} {a : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F x) :
    ContinuousOn (deriv F) (Icc (0 : ℝ) a) := by
  intro x hx
  exact ((hF x hx).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt

theorem n05_optical_deriv_lipschitz {F : ℝ → ℝ} {a : ℝ} {M : NNReal}
    (hF : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F x)
    (hM : ∀ x ∈ Icc (0 : ℝ) a, |deriv (deriv F) x| ≤ M) :
    LipschitzOnWith M (deriv F) (Icc (0 : ℝ) a) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x hx => ((hF x hx).derivWithin (m := 1)
      (by norm_num)).differentiableAt (by norm_num)) _ (convex_Icc 0 a)
  intro x hx
  change ‖deriv (deriv F) x‖ ≤ (M : ℝ)
  simpa only [Real.norm_eq_abs] using hM x hx

theorem n05OpticalRootQuotient_integrable {F : ℝ → ℝ} {a x : ℝ}
    (hF : ContinuousOn (deriv F) (Icc (0 : ℝ) a)) (hx : x ∈ Icc (0 : ℝ) a) :
    IntervalIntegrable (fun t => deriv F (t * x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  exact hF.comp (continuous_id.mul continuous_const).continuousOn
    (fun t ht => n05_optical_unit_mul_mem hx ht)

/-- No quotient is used at zero. The identity follows from the actual
fundamental theorem of calculus and affine interval substitution. -/
theorem n05OpticalRootQuotient_mul {F : ℝ → ℝ} {a x : ℝ}
    (hF : ∀ y ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F y)
    (hzero : F 0 = 0) (hx : x ∈ Icc (0 : ℝ) a) :
    x * n05OpticalRootQuotient F x = F x := by
  have hsub : Icc (0 : ℝ) x ⊆ Icc (0 : ℝ) a := Icc_subset_Icc le_rfl hx.2
  have hint : IntervalIntegrable (deriv F) volume 0 x :=
    ((n05_optical_deriv_continuousOn hF).mono hsub).intervalIntegrable_of_Icc hx.1
  have hdiff : ∀ t ∈ uIcc (0 : ℝ) x, DifferentiableAt ℝ F t := by
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact (hF t (hsub ht)).differentiableAt (by norm_num)
  have hFTC : (∫ t in (0 : ℝ)..x, deriv F t) = F x := by
    simpa only [hzero, sub_zero] using intervalIntegral.integral_deriv_eq_sub hdiff hint
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun t => deriv F t) (a := (0 : ℝ)) (b := 1) x
  simpa only [n05OpticalRootQuotient, smul_eq_mul, zero_mul, one_mul, hFTC] using hscale

/-- A second derivative bound controls differences of the extended root
quotient. A coarse constant avoids any endpoint division. -/
theorem n05OpticalRootQuotient_lipschitz {F : ℝ → ℝ} {a : ℝ} {M : NNReal}
    (hF : ContinuousOn (deriv F) (Icc (0 : ℝ) a))
    (hM : LipschitzOnWith M (deriv F) (Icc (0 : ℝ) a)) :
    LipschitzOnWith M (n05OpticalRootQuotient F) (Icc (0 : ℝ) a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hiX := n05OpticalRootQuotient_integrable hF hx
  have hiY := n05OpticalRootQuotient_integrable hF hy
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |deriv F (t * x) - deriv F (t * y)| ≤ (M : ℝ) * |x - y| := by
    have hb := hM.dist_le_mul (t * x) (n05_optical_unit_mul_mem hx ht)
      (t * y) (n05_optical_unit_mul_mem hy ht)
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg ht.1] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (by nlinarith only [ht.2, abs_nonneg (x - y)] :
        t * |x - y| ≤ |x - y|) M.coe_nonneg)
  have hbound := intervalIntegral.integral_mono_on zero_le_one
    ((hiX.sub hiY).abs) intervalIntegrable_const hp
  change |n05OpticalRootQuotient F x - n05OpticalRootQuotient F y| ≤
    (M : ℝ) * |x - y|
  unfold n05OpticalRootQuotient
  rw [← intervalIntegral.integral_sub hiX hiY]
  exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (by simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hbound)

theorem n05OpticalRootQuotient_abs_le {F : ℝ → ℝ} {a x B : ℝ}
    (hF : ContinuousOn (deriv F) (Icc (0 : ℝ) a))
    (hB : ∀ y ∈ Icc (0 : ℝ) a, |deriv F y| ≤ B)
    (hx : x ∈ Icc (0 : ℝ) a) : |n05OpticalRootQuotient F x| ≤ B := by
  have hi := n05OpticalRootQuotient_integrable hF hx
  have hb := intervalIntegral.integral_mono_on zero_le_one hi.abs intervalIntegrable_const
    (fun t ht => hB (t * x) (n05_optical_unit_mul_mem hx ht))
  exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (by simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hb)

/-- The global optical lower bound survives division at the root itself,
by continuity of the integral quotient. -/
theorem n05OpticalRootQuotient_lower {F : ℝ → ℝ} {a κ : ℝ} {M : NNReal}
    (ha : 0 < a) (hF : ∀ y ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F y)
    (hzero : F 0 = 0)
    (hM : LipschitzOnWith M (deriv F) (Icc (0 : ℝ) a))
    (hlower : ∀ y ∈ Icc (0 : ℝ) a, κ * y ≤ F y) :
    ∀ x ∈ Icc (0 : ℝ) a, κ ≤ n05OpticalRootQuotient F x := by
  have hc := (n05OpticalRootQuotient_lipschitz
    (n05_optical_deriv_continuousOn hF) hM).continuousOn
  have ho (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) : κ ≤ n05OpticalRootQuotient F x := by
    have he := n05OpticalRootQuotient_mul hF hzero (Ioo_subset_Icc_self hx)
    have hb := hlower x (Ioo_subset_Icc_self hx)
    rw [← he, mul_comm κ x] at hb
    exact le_of_mul_le_mul_left hb hx.1
  have hclosure : closure (Ioo (0 : ℝ) a) = Icc (0 : ℝ) a := closure_Ioo ha.ne
  intro x hx
  apply le_on_closure ho continuousOn_const
    (by simpa only [hclosure] using hc)
  simpa only [hclosure] using hx

/-- The derivative at the outer endpoint of a root segment differs from
the averaged derivative by at most the second-derivative scale times its length. -/
theorem n05OpticalRootQuotient_deriv_sub_le {F : ℝ → ℝ} {a x : ℝ} {M : NNReal}
    (hF : ContinuousOn (deriv F) (Icc (0 : ℝ) a))
    (hM : LipschitzOnWith M (deriv F) (Icc (0 : ℝ) a))
    (hx : x ∈ Icc (0 : ℝ) a) :
    |deriv F x - n05OpticalRootQuotient F x| ≤ (M : ℝ) * x := by
  have hi := n05OpticalRootQuotient_integrable hF hx
  have he : deriv F x - n05OpticalRootQuotient F x =
      ∫ t in (0 : ℝ)..1, deriv F x - deriv F (t * x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp only [n05OpticalRootQuotient, intervalIntegral.integral_const, sub_zero, one_smul]
  rw [he]
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |deriv F x - deriv F (t * x)| ≤ (M : ℝ) * x := by
    have hm := hM.dist_le_mul x hx (t * x) (n05_optical_unit_mul_mem hx ht)
    rw [Real.dist_eq, Real.dist_eq] at hm
    have htx : 0 ≤ x - t * x := by nlinarith only [ht.2, hx.1]
    rw [abs_of_nonneg htx] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left
      (by nlinarith only [mul_nonneg ht.1 hx.1] : x - t * x ≤ x) M.coe_nonneg)
  have hm := intervalIntegral.integral_mono_on zero_le_one
    ((intervalIntegrable_const.sub hi).abs) intervalIntegrable_const hb
  exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (by simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hm)

/-- Equal positive optical travel keeps the cut away from both roots.
The speed bound is given in squared form to avoid fractional powers in
the resulting distance constant. -/
theorem n05_optical_equal_cut_distance {F : ℝ → ℝ} {l c u B τ : ℝ}
    (hlc : l < c) (hcu : c < u) (hB : 0 < B)
    (hF : ContinuousOn F (Icc l u))
    (hupper : ∀ r ∈ Icc l u, F r ≤ B ^ 2)
    (hleft : τ / 2 ≤ ∫ r in l..c, Real.sqrt (F r))
    (hright : τ / 2 ≤ ∫ r in c..u, Real.sqrt (F r)) :
    τ / (2 * B) ≤ c - l ∧ τ / (2 * B) ≤ u - c := by
  have hc : ContinuousOn (fun r => Real.sqrt (F r)) (Icc l u) :=
    Real.continuous_sqrt.comp_continuousOn hF
  have hb (r : ℝ) (hr : r ∈ Icc l u) : Real.sqrt (F r) ≤ B :=
    (Real.sqrt_le_left hB.le).mpr (hupper r hr)
  have hL := intervalIntegral.integral_mono_on (μ := volume) hlc.le
    ((hc.mono (Icc_subset_Icc le_rfl hcu.le)).intervalIntegrable_of_Icc hlc.le)
    intervalIntegrable_const (fun r hr => hb r ⟨hr.1, hr.2.trans hcu.le⟩)
  have hR := intervalIntegral.integral_mono_on (μ := volume) hcu.le
    ((hc.mono (Icc_subset_Icc hlc.le le_rfl)).intervalIntegrable_of_Icc hcu.le)
    intervalIntegrable_const (fun r hr => hb r ⟨hlc.le.trans hr.1, hr.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hL hR
  change (∫ r in l..c, Real.sqrt (F r)) ≤ (c - l) * B at hL
  change (∫ r in c..u, Real.sqrt (F r)) ≤ (u - c) * B at hR
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num) hB)).mpr
    nlinarith only [hleft, hL]
  · apply (div_le_iff₀ (mul_pos (by norm_num) hB)).mpr
    nlinarith only [hright, hR]

/-- On a half whose opposite root is at least `δ` away, the two-root
distance controls the chosen root distance by the explicit factor `δ/L`. -/
theorem n05_optical_root_distance_lower {L δ x α : ℝ}
    (hL : 0 < L) (hδ : 0 ≤ δ) (hδL : δ ≤ L)
    (hx : 0 ≤ x) (hxd : x ≤ L - δ) (hα : 0 ≤ α) :
    (α * δ / L) * x ≤ α * min x (L - x) := by
  have hxL : x ≤ L := by linarith only [hxd, hδ]
  have hfirst : δ * x ≤ L * x := mul_le_mul_of_nonneg_right hδL hx
  have hsecond : δ * x ≤ L * (L - x) := by
    have h1 := mul_le_mul_of_nonneg_left hxL hδ
    have h2 := mul_le_mul_of_nonneg_left (show δ ≤ L - x by linarith only [hxd]) hL.le
    nlinarith only [h1, h2]
  have hmin : δ / L * x ≤ min x (L - x) := by
    rw [div_mul_eq_mul_div]
    apply le_min
    · exact (div_le_iff₀ hL).mpr (by nlinarith only [hfirst])
    · exact (div_le_iff₀ hL).mpr (by nlinarith only [hsecond])
  convert mul_le_mul_of_nonneg_left hmin hα using 1 <;> ring

end ContinuousFlexibility.Statements
