import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative
import ContinuousFlexibility.Analysis.PositiveHeightTaylorInterpolation

/-!
# Reference identities for the actual radial Taylor data

A genuine joint identity germ determines every radial trace. The
displayed finite polynomials therefore reproduce the two projections,
and a unit height germ makes the logarithmic interpolation exactly one.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem radialBoundaryJet_eq_of_joint_germ
    {F G : PolarPoint → ℝ} {c : ℝ}
    (h : ∀ θ, F =ᶠ[𝓝 (c, θ)] G) (j : ℕ) (θ : ℝ) :
    radialBoundaryJet F c j θ = radialBoundaryJet G c j θ := by
  have hline : Tendsto (fun x : ℝ => (x, θ)) (𝓝 c) (𝓝 (c, θ)) :=
    (continuous_id.prodMk continuous_const).tendsto c
  exact ((h θ).comp_tendsto hline).iteratedDeriv_eq j

theorem boundaryTaylorPolynomial_snd (n : ℕ) (c : ℝ) :
    boundaryTaylorPolynomial n c (radialBoundaryJet (Prod.snd : PolarPoint → ℝ) c) =
      (Prod.snd : PolarPoint → ℝ) := by
  funext p
  unfold boundaryTaylorPolynomial
  rw [Finset.sum_eq_single 0]
  · simp only [radialBoundaryJet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one]
  · intro j _ hj
    simp only [radialBoundaryJet, iteratedDeriv_const, if_neg hj, zero_div, zero_mul]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.succ_pos n))).elim

theorem boundaryTaylorPolynomial_fst (n : ℕ) (c : ℝ) :
    boundaryTaylorPolynomial (n + 1) c (radialBoundaryJet (Prod.fst : PolarPoint → ℝ) c) =
      (Prod.fst : PolarPoint → ℝ) := by
  funext p
  have hterm (j : ℕ) :
      radialBoundaryJet (Prod.fst : PolarPoint → ℝ) c j p.2 /
          (j.factorial : ℝ) * (p.1 - c) ^ j =
        (if j = 0 then c else 0) + (if j = 1 then p.1 - c else 0) := by
    by_cases hj0 : j = 0
    · subst j
      simp only [radialBoundaryJet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, pow_zero, mul_one, if_pos rfl, Nat.zero_ne_one, ite_false, add_zero]
    · by_cases hj1 : j = 1
      · subst j
        simp only [radialBoundaryJet, iteratedDeriv_fun_id, Nat.factorial_one,
          Nat.cast_one, div_one, pow_one, one_mul, Nat.one_ne_zero, ite_false, if_pos rfl,
          zero_add]
      · simp only [radialBoundaryJet, iteratedDeriv_fun_id, if_neg hj0, if_neg hj1,
          zero_div, zero_mul, zero_add]
  have hzero : 0 ∈ Finset.range (n + 1 + 1) := Finset.mem_range.mpr (by omega)
  have hone : 1 ∈ Finset.range (n + 1 + 1) := Finset.mem_range.mpr (by omega)
  simp only [boundaryTaylorPolynomial, hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', hzero, hone, ite_true]
  ring

theorem oneSidedBoundaryTaylorRepresentative_eq_snd
    {F : PolarPoint → ℝ} {c : ℝ}
    (h : ∀ θ, F =ᶠ[𝓝 (c, θ)] (Prod.snd : PolarPoint → ℝ)) (n : ℕ) :
    oneSidedBoundaryTaylorRepresentative n c F = (Prod.snd : PolarPoint → ℝ) := by
  have he : radialBoundaryJet F c = radialBoundaryJet (Prod.snd : PolarPoint → ℝ) c := by
    funext j θ
    exact radialBoundaryJet_eq_of_joint_germ h j θ
  rw [oneSidedBoundaryTaylorRepresentative, he, boundaryTaylorPolynomial_snd]

theorem oneSidedBoundaryTaylorRepresentative_eq_fst
    {F : PolarPoint → ℝ} {c : ℝ}
    (h : ∀ θ, F =ᶠ[𝓝 (c, θ)] (Prod.fst : PolarPoint → ℝ)) (n : ℕ) :
    oneSidedBoundaryTaylorRepresentative (n + 1) c F = (Prod.fst : PolarPoint → ℝ) := by
  have he : radialBoundaryJet F c = radialBoundaryJet (Prod.fst : PolarPoint → ℝ) c := by
    funext j θ
    exact radialBoundaryJet_eq_of_joint_germ h j θ
  rw [oneSidedBoundaryTaylorRepresentative, he, boundaryTaylorPolynomial_fst]

theorem positiveHeightTaylorInterpolation_reference_one
    (n : ℕ) (l r δ : ℝ) {h : Bool → PolarPoint → ℝ}
    (hOne : ∀ side θ, h side =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ))) :
    positiveHeightTaylorInterpolation n l r δ (fun _ => 1) h = (fun _ => (1 : ℝ)) := by
  have hzero (side : Bool) (j : ℕ) (θ : ℝ) :
      positiveHeightTaylorData l r (fun _ => 1) h side j θ = 0 := by
    have hlog : ∀ η, boundaryHeightLogRatio (fun _ => 1) (h side) =ᶠ[
        𝓝 (if side then r else l, η)] (fun _ : PolarPoint => (0 : ℝ)) := by
      intro η
      filter_upwards [hOne side η] with p hp
      simp only [boundaryHeightLogRatio, hp, div_one, Real.log_one]
    have he := radialBoundaryJet_eq_of_joint_germ hlog j θ
    simpa only [positiveHeightTaylorData, radialBoundaryJet,
      iteratedDeriv_fun_const_zero] using he
  funext p
  simp only [positiveHeightTaylorInterpolation, endpointTaylorCorrection,
    boundaryTaylorPolynomial, hzero, zero_div, zero_mul,
    Finset.sum_const_zero, add_zero, Real.exp_zero, mul_one]

end ContinuousFlexibility.Analysis

