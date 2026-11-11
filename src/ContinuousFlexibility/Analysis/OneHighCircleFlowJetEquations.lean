import ContinuousFlexibility.Analysis.OneHighCircleFlowJets
import ContinuousFlexibility.Analysis.OneHighCircleFlowInterior

/-!
# The genuine equations of the angular flow jets

Joint interior smoothness permits commuting the actual time and angular
derivatives. The original trajectory equation therefore determines every
angular jet equation. Compact time reparametrization also proves the
continuity of its source at the endpoints, so the fundamental theorem of
calculus applies on the entire original interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem circleFlow_continuousOn_composedAngularJet
    {G Θ H : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (hH : ContDiff ℝ ∞ H) (n : ℕ) :
    ContinuousOn (fun p : PolarPoint =>
      iteratedDeriv n (fun η => H (p.1, Θ (p.1, η))) p.2)
      (Icc a b ×ˢ (univ : Set ℝ)) := by
  by_cases hab : a ≤ b
  · have hΨ := contDiff_circleFlow_timeChange hG hP hperiod hΘ hinit hflow
      (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
      (circleFlowCompactTime_mem hab)
    have hsmooth : ContDiff ℝ ∞ (fun p : PolarPoint =>
        H (circleFlowCompactTime a b p.1, Θ (circleFlowCompactTime a b p.1, p.2))) :=
      hH.comp (((contDiff_circleFlowCompactTime a b).comp contDiff_fst).prodMk hΨ)
    have hjet : Continuous (fun p : PolarPoint =>
        iteratedDeriv n (fun η =>
          H (circleFlowCompactTime a b p.1, Θ (circleFlowCompactTime a b p.1, η))) p.2) := by
      have hc := (contDiffOn_univ.mp
        (Statements.contDiffOn_mixedDerivative isOpen_univ hsmooth.contDiffOn 0 n)).continuous
      exact hc.congr (fun p => by simp only [Statements.mixedDerivative, iteratedDeriv_zero])
    exact continuousOn_of_compact_time_reparam
      (contDiff_circleFlowCompactTime a b).continuous
      (fun s _ => circleFlowCompactTime_mem hab s) (circleFlowCompactTime_surjOn a b) hjet
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), empty_prod]
    exact continuousOn_empty _

/-- The actual `n`th angular derivative solves the equation obtained by
applying that same angular derivative to the original composed speed. -/
theorem circleFlow_hasDerivAt_angularJet_time {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) (θ : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (fun η => Θ (r, η)) θ)
      (iteratedDeriv n (fun η => G (t, Θ (t, η))) θ) t := by
  have hU : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hs := circleFlow_contDiffOn_open hG hP hperiod hΘ hinit hflow
  have hjet := Statements.contDiffOn_mixedDerivative hU hs 0 n
  have hd0 := ((hjet.contDiffAt (hU.mem_nhds ⟨ht, mem_univ θ⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ))
  have hd : HasDerivAt (fun r => iteratedDeriv n (fun η => Θ (r, η)) θ)
      (deriv (fun r => iteratedDeriv n (fun η => Θ (r, η)) θ) t) t := by
    have he : (Statements.mixedDerivative 0 n Θ ∘ (fun r : ℝ => (id r, θ))) =
        fun r => iteratedDeriv n (fun η => Θ (r, η)) θ := by
      funext r
      simp only [Function.comp_apply, id_eq, Statements.mixedDerivative, iteratedDeriv_zero]
    rw [he] at hd0
    exact hd0.differentiableAt.hasDerivAt
  have heq : (fun η => radialPartial Θ (t, η)) = fun η => G (t, Θ (t, η)) := by
    funext η
    have hpartial : HasDerivAt (fun r => Θ (r, η)) (radialPartial Θ (t, η)) t :=
      ((circleFlow_contDiffAt (p := (t, η)) hG hP hperiod hΘ hinit hflow ht).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t η))
    exact hpartial.unique (hflow t ht η)
  have hcomm := Statements.mixedDerivative_radialPartial hU hs 0 n
    (p := (t, θ)) ⟨ht, mem_univ θ⟩
  apply hd.congr_deriv
  simpa only [Statements.mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
    Nat.zero_add, heq] using hcomm.symm

/-- The integral equation for every actual angular jet, valid up to both
endpoints of the original time interval. -/
theorem circleFlow_angularJet_integral_eq {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    iteratedDeriv n (fun η => Θ (t, η)) θ = iteratedDeriv n id θ +
      ∫ r in a..t, iteratedDeriv n (fun η => G (r, Θ (r, η))) θ := by
  have hjet : ContinuousOn (fun r => iteratedDeriv n (fun η => Θ (r, η)) θ) (Icc a b) :=
    (circleFlow_continuousOn_angularJet hG hP hperiod hΘ hinit hflow n).comp
      (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ θ⟩)
  have hsource : ContinuousOn
      (fun r => iteratedDeriv n (fun η => G (r, Θ (r, η))) θ) (Icc a b) :=
    (circleFlow_continuousOn_composedAngularJet hG hP hperiod hΘ hinit hflow hG n).comp
      (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ θ⟩)
  have hderiv (r : ℝ) (hr : r ∈ Ioo a t) :=
    circleFlow_hasDerivAt_angularJet_time hG hP hperiod hΘ hinit hflow n
      ⟨hr.1, hr.2.trans_le ht.2⟩ θ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hjet.mono (Icc_subset_Icc le_rfl ht.2)) hderiv
    ((hsource.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
  have hinitial : (fun η => Θ (a, η)) = id := funext hinit
  rw [hinitial] at hFTC
  linarith

end ContinuousFlexibility.Analysis
