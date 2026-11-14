module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowJetBoundsBasic
public import ContinuousFlexibility.Analysis.OneHighCircleFlowJetEquations
public import ContinuousFlexibility.Analysis.OneHighCircleFlowGronwall

/-!
# Actual flow jets controlled by integrated speed derivatives

The induction uses the triangular actual chain rule and the integral
equations of the supplied flow. Its constants depend on the integral of
a common speed-derivative envelope, uniformly in physical time and the
initial angle. The speed itself, and hence the mean rotation, does not
enter the estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

private theorem circleFlow_integral_le_total {B : ℝ → ℝ} {a b t : ℝ}
    (hB : ContinuousOn B (Icc a b)) (hBpos : ∀ r ∈ Icc a b, 0 ≤ B r)
    (ht : t ∈ Icc a b) : (∫ r in a..t, B r) ≤ ∫ r in a..b, B r := by
  have hat : IntervalIntegrable B volume a t :=
    (hB.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have htb : IntervalIntegrable B volume t b :=
    (hB.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  rw [← intervalIntegral.integral_add_adjacent_intervals hat htb]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg ht.2
    (fun r hr => hBpos r ⟨ht.1.trans hr.1, hr.2⟩))

private theorem circleFlow_continuousOn_verticalSlice {f : PolarPoint → ℝ}
    {a b θ : ℝ} (hf : ContinuousOn f (Icc a b ×ˢ (univ : Set ℝ))) :
    ContinuousOn (fun r : ℝ => f (r, θ)) (Icc a b) := by
  have hpair : ContinuousOn (fun r : ℝ => (r, θ)) (Icc a b) :=
    continuousOn_id.prodMk continuousOn_const
  exact hf.comp hpair (fun r hr => ⟨hr, mem_univ θ⟩)

/-- A scalar estimate used for each actual angular jet. Its hypotheses
are discharged below by the genuine jet integral equation and chain rule. -/
private theorem circleFlow_scalarJet_bound {u q B : ℝ → ℝ} {a b t c D K : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hB : ContinuousOn B (Icc a b)) (hBpos : ∀ r ∈ Icc a b, 0 ≤ B r)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (n : ℕ) (hc : |c| ≤ 1)
    (heq : ∀ r ∈ Icc a b, u r = c + ∫ s in a..r, q s)
    (hchain : ∀ r ∈ Icc a b, |q r| ≤ D * B r * (|u r| + K ^ n))
    (ht : t ∈ Icc a b) :
    |u t| ≤ (1 + D * K ^ n * (∫ r in a..b, B r)) *
      Real.exp (D * ∫ r in a..b, B r) := by
  have hright : ContinuousOn
      (fun r => D * B r * |u r| + D * B r * K ^ n) (Icc a b) :=
    ((continuousOn_const.mul hB).mul hu.abs).add
      ((continuousOn_const.mul hB).mul continuousOn_const)
  have hlin (τ : ℝ) (hτ : τ ∈ Icc a t) :
      |u τ| ≤ 1 + ∫ r in a..τ, D * B r * |u r| + D * B r * K ^ n := by
    have hτab : τ ∈ Icc a b := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hqI : IntervalIntegrable (fun r => |q r|) volume a τ :=
      (hq.abs.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1
    have hrI : IntervalIntegrable
        (fun r => D * B r * |u r| + D * B r * K ^ n) volume a τ :=
      (hright.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hτ.1 hqI hrI
      (fun r hr => by
        simpa only [mul_add] using hchain r ⟨hr.1, hr.2.trans hτab.2⟩)
    calc
      |u τ| = |c + ∫ r in a..τ, q r| := by rw [heq τ hτab]
      _ ≤ |c| + |∫ r in a..τ, q r| := abs_add_le _ _
      _ ≤ 1 + ∫ r in a..τ, |q r| :=
        add_le_add hc (intervalIntegral.abs_integral_le_integral_abs (μ := volume) hτ.1)
      _ ≤ _ := add_le_add le_rfl hmono
  have hgronwall := integral_gronwall_of_continuousOn ht.1
    (hu.abs.mono (Icc_subset_Icc le_rfl ht.2))
    ((continuousOn_const.mul hB).mono (Icc_subset_Icc le_rfl ht.2))
    (((continuousOn_const.mul hB).mul continuousOn_const).mono
      (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => mul_nonneg hD (hBpos r ⟨hr.1, hr.2.trans ht.2⟩))
    (fun r hr => mul_nonneg (mul_nonneg hD (hBpos r ⟨hr.1, hr.2.trans ht.2⟩))
      (pow_nonneg hK n)) hlin
  have hshort : (∫ r in a..t, B r) ≤ ∫ r in a..b, B r :=
    circleFlow_integral_le_total hB hBpos ht
  have hfirst : 1 + D * K ^ n * (∫ r in a..t, B r) ≤
      1 + D * K ^ n * (∫ r in a..b, B r) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hshort (mul_nonneg hD (pow_nonneg hK n)))
  have hexp : Real.exp (D * ∫ r in a..t, B r) ≤ Real.exp (D * ∫ r in a..b, B r) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hshort hD)
  have hL : 0 ≤ ∫ r in a..b, B r :=
    intervalIntegral.integral_nonneg (μ := volume) (ht.1.trans ht.2) hBpos
  calc
    |u t| ≤ (1 + ∫ r in a..t, D * B r * K ^ n) *
        Real.exp (∫ r in a..t, D * B r) := hgronwall
    _ = (1 + D * K ^ n * (∫ r in a..t, B r)) *
        Real.exp (D * ∫ r in a..t, B r) := by
      simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
      ring
    _ ≤ _ := mul_le_mul hfirst hexp (Real.exp_pos _).le (by positivity)

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
    have hu : ContinuousOn
        (fun r => iteratedDeriv (N + 1) (fun η => Θ (r, η)) θ) (Icc a b) :=
      circleFlow_continuousOn_verticalSlice
        (circleFlow_continuousOn_angularJet
          (G := G) (Θ := Θ) (a := a) (b := b) (P := P)
          hG hP hperiod hΘ hinit hflow (N + 1))
    have hsource : ContinuousOn
        (fun r => iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ) (Icc a b) :=
      circleFlow_continuousOn_verticalSlice
        (circleFlow_continuousOn_composedAngularJet
          (G := G) (Θ := Θ) (H := G) (a := a) (b := b) (P := P)
          hG hP hperiod hΘ hinit hflow hG (N + 1))
    have hchain (r : ℝ) (hr : r ∈ Icc a b) :
        |iteratedDeriv (N + 1) (fun η => G (r, Θ (r, η))) θ| ≤
          D * B r * (|iteratedDeriv (N + 1) (fun η => Θ (r, η)) θ| + K ^ (N + 1)) := by
      have hc := circleFlow_norm_iteratedDeriv_comp_le_linear_top
        (g := fun η => G (r, η)) (h := fun η => Θ (r, η)) (n := N + 1) (B := B r) (K := K)
        (hG.comp (contDiff_const.prodMk contDiff_id))
        (circleFlow_contDiff_angle hG hP hperiod hΘ hinit hflow hr)
        (Nat.succ_pos N) (hBpos r hr) hK
        (fun k hk hkN η => by simpa only [Real.norm_eq_abs] using hspeed r hr k hk hkN η)
        (fun k hk hkN η => by
          simpa only [Real.norm_eq_abs] using hprevious r hr k hk (by omega) η) θ
      simpa only [Real.norm_eq_abs, Function.comp_def, D] using hc
    have hinitial : |iteratedDeriv (N + 1) (id : ℝ → ℝ) θ| ≤ 1 := by
      rw [iteratedDeriv_id, if_neg (Nat.succ_ne_zero N)]
      split_ifs <;> norm_num
    have hbound := circleFlow_scalarJet_bound hu hsource hB hBpos hD hKnonneg
      (N + 1) hinitial
      (fun r hr => circleFlow_angularJet_integral_eq hG hP hperiod hΘ hinit hflow (N + 1) hr θ)
      hchain ht
    exact hbound.trans (by
      rw [circleFlowJetBound]
      exact le_add_of_nonneg_left hKnonneg)

end ContinuousFlexibility.Analysis
