import ContinuousFlexibility.Analysis.ScalarSpatialIntegralRegularity

/-!
# Actual angular smoothness with merely continuous time dependence

The true angular Jacobian supplied by the parameter variational formula
is bootstrapped using composition and compact integration to every angular
order. A continuous time clamp
includes both endpoints without differentiating the field in time.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Every closed-time slice is genuinely smooth, and all actual angular
jets are jointly continuous up to both time endpoints. The supplied
variational formula is a true first derivative; no higher flow jet is input. -/
theorem scalarFlow_angularSmooth_of_variationalFormula
    {F Θ : PolarPoint → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ n : ℕ, ScalarSpatialRegularity n F)
    (hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ Icc a b))
    (hfirst : ∀ x t : ℝ, t ∈ Icc a b →
      HasDerivAt (fun y => Θ (y, t))
        (Real.exp (∫ r in a..t, scalarSpatialDerivative F (Θ (x, r), r))) x) :
    (∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => Θ (x, t))) ∧
      ∀ n : ℕ, ContinuousOn
        (fun p : PolarPoint => iteratedDeriv n (fun x => Θ (x, p.2)) p.1)
        ((univ : Set ℝ) ×ˢ Icc a b) := by
  let τ : ℝ → ℝ := fun t => max a (min t b)
  have hτ : Continuous τ := continuous_const.max (continuous_id.min continuous_const)
  have hτmem (t : ℝ) : τ t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hτeq (t : ℝ) (ht : t ∈ Icc a b) : τ t = t := by
    dsimp only [τ]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let Ψ : PolarPoint → ℝ := fun p => Θ (p.1, τ p.2)
  have hΨ : Continuous Ψ :=
    hΘ.comp_continuous (continuous_fst.prodMk (hτ.comp continuous_snd))
      (fun p => ⟨mem_univ p.1, hτmem p.2⟩)
  have hΨeq (x t : ℝ) (ht : t ∈ Icc a b) : Ψ (x, t) = Θ (x, t) := by
    change Θ (x, τ t) = Θ (x, t)
    rw [hτeq t ht]
  let D : PolarPoint → ℝ := scalarSpatialDerivative F
  let K : PolarPoint → ℝ := fun p => D (Ψ p, p.2)
  let I : PolarPoint → ℝ := fun p => ∫ t in a..p.2, K (p.1, t)
  have hderiv (x t : ℝ) : HasDerivAt (fun y => Ψ (y, t))
      (Real.exp (I (x, τ t))) x := by
    change HasDerivAt (fun y => Θ (y, τ t)) (Real.exp (I (x, τ t))) x
    apply (hfirst x (τ t) (hτmem t)).congr_deriv
    apply congrArg Real.exp
    change (∫ r in a..τ t, D (Θ (x, r), r)) = ∫ r in a..τ t, K (x, r)
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a (τ t) := by
      simpa only [uIcc_of_le (hτmem t).1] using hr
    change D (Θ (x, r), r) = D (Ψ (x, r), r)
    rw [hΨeq x r ⟨hr'.1, hr'.2.trans (hτmem t).2⟩]
  have hregular (n : ℕ) : ScalarSpatialRegularity n Ψ := by
    induction n with
    | zero => exact hΨ
    | succ n ih =>
        refine ⟨hΨ, fun x t => (hderiv x t).differentiableAt, ?_⟩
        have hK : ScalarSpatialRegularity n K := ((hF (n + 1)).2.2).comp ih
        have hI : ScalarSpatialRegularity n I := hK.primitive a
        have he : scalarSpatialDerivative Ψ =
            fun p : PolarPoint => Real.exp (I (p.1, τ p.2)) := by
          funext p
          exact (hderiv p.1 p.2).deriv
        rw [he]
        exact (hI.time_comp hτ).exp
  have hslice (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x => Ψ (x, t)) = (fun x => Θ (x, t)) :=
    funext (fun x => hΨeq x t ht)
  constructor
  · intro t ht
    have hs := contDiff_spatialSlice_of_all_regularity hregular t
    rw [hslice t ht] at hs
    exact hs
  · intro n
    have hc : ContinuousOn
        (fun p : PolarPoint => iteratedDeriv n (fun x => Ψ (x, p.2)) p.1)
        ((univ : Set ℝ) ×ˢ Icc a b) :=
      ((hregular n).continuous_iteratedDeriv n le_rfl).continuousOn
    apply hc.congr
    intro p hp
    change iteratedDeriv n (fun x => Θ (x, p.2)) p.1 =
      iteratedDeriv n (fun x => Ψ (x, p.2)) p.1
    rw [hslice p.2 hp.2]

end ContinuousFlexibility.Analysis
