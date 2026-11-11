import ContinuousFlexibility.Analysis.OneHighCircleFlowJetBoundsBasic
import ContinuousFlexibility.Analysis.OneHighCircleFlowJetEquations
import ContinuousFlexibility.Analysis.OneHighCircleFlowGronwall

/-!
# Actual flow jets controlled by integrated speed derivatives

The induction uses the triangular actual chain rule and the integral
equations of the supplied flow. Its constants depend on the integral of
a common speed-derivative envelope, uniformly in physical time and the
initial angle. The speed itself, and hence the mean rotation, does not
enter the estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

private theorem circleFlow_integral_le_total {B : ℝ → ℝ} {a b t : ℝ}
    (hB : ContinuousOn B (Icc a b)) (hBpos : ∀ r ∈ Icc a b, 0 ≤ B r)
    (ht : t ∈ Icc a b) : (∫ r in a..t, B r) ≤ ∫ r in a..b, B r := by
  have hat := (hB.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have htb := (hB.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  rw [← intervalIntegral.integral_add_adjacent_intervals hat htb]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg ht.2
    (fun r hr => hBpos r ⟨ht.1.trans hr.1, hr.2⟩))

/-- Every finite group of actual flow jets is bounded by an explicit
function of the integrated envelope for those speed derivatives. -/
theorem circleFlow_angularJets_le_bound {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {B : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hBpos : ∀ t ∈ Icc a b, 0 ≤ B t) (N : ℕ)
    (hspeed : ∀ t ∈ Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ N →
      ∀ θ : ℝ, |iteratedDeriv j (fun η => G (t, η)) θ| ≤ B t) :
    ∀ t ∈ Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ N → ∀ θ : ℝ,
      |iteratedDeriv j (fun η => Θ (t, η)) θ| ≤
        circleFlowJetBound N (∫ r in a..b, B r) := by
  classical
  have hL : 0 ≤ ∫ r in a..b, B r := intervalIntegral.integral_nonneg hab hBpos
  revert hspeed
  induction N with
  | zero =>
    intro _ t ht j hj hjN θ
    omega
  | succ N ih =>
    intro hspeed
    have hprevious := ih (fun t ht j hj hjN θ =>
      hspeed t ht j hj (hjN.trans (Nat.le_succ N)) θ)
    let K : ℝ := circleFlowJetBound N (∫ r in a..b, B r)
    let D : ℝ := Fintype.card (OrderedFinpartition (N + 1))
    have hK : 1 ≤ K := circleFlowJetBound_one_le N hL
    have hKnonneg : 0 ≤ K := zero_le_one.trans hK
    have hD : 0 ≤ D := Nat.cast_nonneg _
    intro t ht j hj hjN θ
    by_cases hjold : j ≤ N
    · exact (hprevious t ht j hj hjold θ).trans (circleFlowJetBound_le_succ N hL)
    have hjtop : j = N + 1 := by omega
    subst j
    let u : ℝ → ℝ := fun r => |iteratedDeriv (N + 1) (fun η => Θ (r, η)) θ|
    have hu : ContinuousOn u (Icc a b) :=
      ((circleFlow_continuousOn_angularJet hG hP hperiod hΘ hinit hflow (N + 1)).comp
        (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ θ⟩)).abs
    have hsource : ContinuousOn
        (fun r => iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ) (Icc a b) :=
      (circleFlow_continuousOn_composedAngularJet hG hP hperiod hΘ hinit hflow hG (N + 1)).comp
        (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ θ⟩)
    have hchain (r : ℝ) (hr : r ∈ Icc a b) :
        |iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ| ≤
          D * B r * (u r + K ^ (N + 1)) := by
      have hc := circleFlow_norm_iteratedDeriv_comp_le_linear_top
        (hG.comp (contDiff_const.prodMk contDiff_id))
        (circleFlow_contDiff_angle hG hP hperiod hΘ hinit hflow hr)
        (Nat.succ_pos N) (hBpos r hr) hK
        (fun k hk hkN η => by simpa only [Real.norm_eq_abs] using hspeed r hr k hk hkN η)
        (fun k hk hkN η => by
          simpa only [Real.norm_eq_abs] using hprevious r hr k hk (by omega) η) θ
      simpa only [Real.norm_eq_abs] using hc
    have hinitial : |iteratedDeriv (N + 1) (id : ℝ → ℝ) θ| ≤ 1 := by
      rw [iteratedDeriv_id, if_neg (Nat.succ_ne_zero N)]
      split_ifs <;> norm_num
    have hright : ContinuousOn
        (fun r => D * B r * u r + D * B r * K ^ (N + 1)) (Icc a b) :=
      ((continuousOn_const.mul hB).mul hu).add
        ((continuousOn_const.mul hB).mul continuousOn_const)
    have hlin (τ : ℝ) (hτ : τ ∈ Icc a t) :
        u τ ≤ 1 + ∫ r in a..τ, D * B r * u r + D * B r * K ^ (N + 1) := by
      have hτab : τ ∈ Icc a b := ⟨hτ.1, hτ.2.trans ht.2⟩
      have hmono := intervalIntegral.integral_mono_on (μ := volume) hτ.1
        ((hsource.abs.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
        ((hright.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
        (fun r hr => by
          simpa only [mul_add] using hchain r ⟨hr.1, hr.2.trans hτab.2⟩)
      calc
        u τ = |iteratedDeriv (N + 1) id θ +
            ∫ r in a..τ, iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ| := by
          dsimp only [u]
          rw [circleFlow_angularJet_integral_eq hG hP hperiod hΘ hinit hflow (N + 1) hτab θ]
        _ ≤ |iteratedDeriv (N + 1) id θ| +
            |∫ r in a..τ, iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ| :=
          abs_add_le _ _
        _ ≤ 1 + ∫ r in a..τ, |iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ| :=
          add_le_add hinitial (intervalIntegral.abs_integral_le_integral_abs (μ := volume) hτ.1)
        _ ≤ _ := add_le_add le_rfl hmono
    have hgronwall := integral_gronwall_of_continuousOn ht.1
      (hu.mono (Icc_subset_Icc le_rfl ht.2))
      ((continuousOn_const.mul hB).mono (Icc_subset_Icc le_rfl ht.2))
      (((continuousOn_const.mul hB).mul continuousOn_const).mono
        (Icc_subset_Icc le_rfl ht.2))
      (fun r hr => mul_nonneg hD (hBpos r ⟨hr.1, hr.2.trans ht.2⟩))
      (fun r hr => mul_nonneg (mul_nonneg hD (hBpos r ⟨hr.1, hr.2.trans ht.2⟩))
        (pow_nonneg hKnonneg (N + 1))) hlin
    have hshort := circleFlow_integral_le_total hB hBpos ht
    have hfirst : 1 + D * K ^ (N + 1) * (∫ r in a..t, B r) ≤
        1 + D * K ^ (N + 1) * (∫ r in a..b, B r) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hshort (mul_nonneg hD (pow_nonneg hKnonneg _)))
    have hexp : Real.exp (D * ∫ r in a..t, B r) ≤ Real.exp (D * ∫ r in a..b, B r) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hshort hD)
    calc
      u t ≤ (1 + ∫ r in a..t, D * B r * K ^ (N + 1)) *
          Real.exp (∫ r in a..t, D * B r) := hgronwall
      _ = (1 + D * K ^ (N + 1) * (∫ r in a..t, B r)) *
          Real.exp (D * ∫ r in a..t, B r) := by
        simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
        ring
      _ ≤ (1 + D * K ^ (N + 1) * (∫ r in a..b, B r)) *
          Real.exp (D * ∫ r in a..b, B r) :=
        mul_le_mul hfirst hexp (Real.exp_pos _).le (by positivity)
      _ ≤ circleFlowJetBound (N + 1) (∫ r in a..b, B r) := by
        rw [circleFlowJetBound]
        exact le_add_of_nonneg_left hKnonneg

end ContinuousFlexibility.Analysis
