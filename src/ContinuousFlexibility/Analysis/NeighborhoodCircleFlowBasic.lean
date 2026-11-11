import ContinuousFlexibility.Analysis.OneHighCircleFlowVariational
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic

/-!
# Scalar circle flows for continuous time coefficients

The characteristic speed can contain a square root of a radial function
vanishing at an endpoint. Only continuity in time is used here; the angular
derivative is supplied as an actual continuous derivative. Picard--Lindelöf
then constructs trajectories on the whole compact time interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- The divided difference formed from the actual angular derivative. -/
def continuousAngleSpeedSecant (dG : PolarPoint → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, dG (p.1, (p.2.2 - p.2.1) * s + p.2.1)

theorem continuous_continuousAngleSpeedSecant {dG : PolarPoint → ℝ}
    (hdG : Continuous dG) : Continuous (continuousAngleSpeedSecant dG) := by
  have hc : Continuous (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
      dG (q.1.1, (q.1.2.2 - q.1.2.1) * q.2 + q.1.2.1)) :=
    hdG.comp
      (continuous_fst.fst.prodMk
        (((continuous_fst.snd.snd.sub continuous_fst.snd.fst).mul continuous_snd).add
          continuous_fst.snd.fst))
  have hi : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      ∫ s in Icc (0 : ℝ) 1, dG (p.1, (p.2.2 - p.2.1) * s + p.2.1)) :=
    continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun (p : ℝ × (ℝ × ℝ)) (s : ℝ) =>
        dG (p.1, (p.2.2 - p.2.1) * s + p.2.1)) hc isCompact_Icc
  simpa only [continuousAngleSpeedSecant,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hi

theorem continuousAngleSpeedSecant_diagonal (dG : PolarPoint → ℝ) (t x : ℝ) :
    continuousAngleSpeedSecant dG (t, (x, x)) = dG (t, x) := by
  simp only [continuousAngleSpeedSecant, sub_self, zero_mul, zero_add,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem continuousAngleSpeed_sub_eq_secant {G dG : PolarPoint → ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (t x y : ℝ) :
    G (t, y) - G (t, x) = continuousAngleSpeedSecant dG (t, (x, y)) * (y - x) := by
  have hc : Continuous (fun r => dG (t, r)) :=
    hdG.comp (continuous_const.prodMk continuous_id)
  have hint : (∫ r in x..y, dG (t, r)) = G (t, y) - G (t, x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv t r)
      (hc.intervalIntegrable x y)
  have hscale := intervalIntegral.smul_integral_comp_mul_add
    (fun r => dG (t, r)) (a := (0 : ℝ)) (b := 1) (y - x) x
  calc
    G (t, y) - G (t, x) = ∫ r in x..y, dG (t, r) := hint.symm
    _ = (y - x) * continuousAngleSpeedSecant dG (t, (x, y)) := by
      simpa only [continuousAngleSpeedSecant, smul_eq_mul, mul_zero, zero_add, mul_one,
        sub_add_cancel] using hscale.symm
    _ = continuousAngleSpeedSecant dG (t, (x, y)) * (y - x) := mul_comm _ _

theorem continuousAngleTrajectory_difference_eq_mul_exp {G dG : PolarPoint → ℝ}
    {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (G (t, u t)) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (G (t, v t)) t) :
    u b - v b = (u a - v a) *
      Real.exp (∫ r in a..b, continuousAngleSpeedSecant dG (r, (v r, u r))) := by
  have hκ : ContinuousOn
      (fun r => continuousAngleSpeedSecant dG (r, (v r, u r))) (Icc a b) :=
    (continuous_continuousAngleSpeedSecant hdG).comp_continuousOn
      (continuousOn_id.prodMk (hv.prodMk hu))
  apply scalar_linearODE_eq_mul_exp hab hκ (hu.sub hv)
  intro r hr
  exact ((hdu r hr).sub (hdv r hr)).congr_deriv
    (continuousAngleSpeed_sub_eq_secant hdG hderiv r (v r) (u r))

theorem continuousAngleFlow_difference_eq_mul_exp {G dG Θ : PolarPoint → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) (η θ : ℝ) :
    Θ (b, η) - Θ (b, θ) = (Θ (a, η) - Θ (a, θ)) *
      Real.exp (∫ r in a..b, continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η)))) :=
  continuousAngleTrajectory_difference_eq_mul_exp hab hdG hderiv (hΘ η) (hΘ θ)
    (fun r hr => hflow r hr η) (fun r hr => hflow r hr θ)

theorem exists_continuous_periodic_strip_bound {F : PolarPoint → ℝ}
    (hF : Continuous F) {P : ℝ} (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => F (t, θ)) P) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ∀ θ : ℝ, |F (t, θ)| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc (0 : ℝ) P) hF.continuousOn
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro t ht θ
  obtain ⟨η, hη, he⟩ := (hperiod t).exists_mem_Ico₀ hP θ
  rw [he]
  have hm : |F (t, η)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (t, η) ⟨ht, ⟨hη.1, hη.2.le⟩⟩
  exact hm.trans (le_max_right _ _)

theorem continuousAngleSpeed_derivative_periodic {G dG : PolarPoint → ℝ} {P : ℝ}
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) (t : ℝ) :
    Function.Periodic (fun θ => dG (t, θ)) P := by
  intro θ
  have he : (fun η => G (t, η + P)) = fun η => G (t, η) := funext (hperiod t)
  calc
    dG (t, θ + P) = deriv (fun η => G (t, η)) (θ + P) := (hderiv t (θ + P)).deriv.symm
    _ = deriv (fun η => G (t, η + P)) θ :=
      (deriv_comp_add_const (fun η => G (t, η)) P θ).symm
    _ = deriv (fun η => G (t, η)) θ := by rw [he]
    _ = dG (t, θ) := (hderiv t θ).deriv

/-- Global angular boundedness lets one choose a Picard ball large enough
for the complete time interval, with no small-time assumption. -/
theorem exists_continuousAngleFlow {G dG : PolarPoint → ℝ} {a b P : ℝ}
    (hab : a ≤ b) (hG : Continuous G) (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hP : 0 < P) (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) :
    ∃ Θ : PolarPoint → ℝ, (∀ θ, Θ (a, θ) = θ) ∧
      (∀ θ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b)) ∧
      (∀ t ∈ Ioo a b, ∀ θ,
        HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) := by
  obtain ⟨M, hM, hbound⟩ := exists_continuous_periodic_strip_bound hG hP hperiod a b
  obtain ⟨K, hK, hdbound⟩ := exists_continuous_periodic_strip_bound hdG hP
    (continuousAngleSpeed_derivative_periodic hderiv hperiod) a b
  have hex (θ : ℝ) : ∃ u : ℝ → ℝ, u a = θ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (G (t, u t)) (Icc a b) t := by
    let L : NNReal := ⟨M, hM⟩
    let K' : NNReal := ⟨K, hK⟩
    let R : NNReal := ⟨M * (b - a), mul_nonneg hM (sub_nonneg.mpr hab)⟩
    have hpl : IsPicardLindelof (fun t x => G (t, x)) ⟨a, le_rfl, hab⟩ θ R 0 L K' := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t ht
        apply LipschitzWith.lipschitzOnWith
        apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hderiv t x).differentiableAt)
        intro x
        change ‖deriv (fun y => G (t, y)) x‖ ≤ K
        rw [(hderiv t x).deriv, Real.norm_eq_abs]
        exact hdbound t ht x
      · intro x _
        exact (hG.comp (continuous_id.prodMk continuous_const)).continuousOn
      · intro t ht x _
        simpa only [L, NNReal.coe_mk, Real.norm_eq_abs] using hbound t ht x
      · change M * max (b - a) (a - a) ≤ M * (b - a) - 0
        rw [sub_self, max_eq_left (sub_nonneg.mpr hab), sub_zero]
    exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose u hu hdu using hex
  refine ⟨fun p => u p.2 p.1, hu, ?_, ?_⟩
  · intro θ t ht
    exact (hdu θ t ht).continuousWithinAt
  · intro t ht θ
    exact (hdu θ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end ContinuousFlexibility.Analysis
