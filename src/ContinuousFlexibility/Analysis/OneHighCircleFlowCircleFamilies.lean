import ContinuousFlexibility.Analysis.OneHighCircleFlowJetEquations
import ContinuousFlexibility.Analysis.OneHighCircleFlowMinkowski
import ContinuousFlexibility.Analysis.OneHighCircleFourierLiftGeometry

/-!
# Canonical circle families for the genuine flow integral equations

On the supplied time interval these are exactly the canonical actual
circle jets of the derivative defect and of the composed speed. The
families are set to zero outside that interval only to give the time
integrals total real-domain functions. All identities and continuity
statements used below are proved on the original interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {P : ℝ} [hP : Fact (0 < P)]

theorem continuous_circleLiftDefectJet_family
    {X : Type*} [TopologicalSpace X] (h : X → ℝ → ℝ)
    (hh : ∀ t, ContDiff ℝ ∞ (h t))
    (hlift : ∀ t, ∀ x, h t (x + P) = h t x + P) (n : ℕ)
    (hj : Continuous (fun p : X × ℝ => iteratedDeriv (n + 1) (h p.1) p.2)) :
    Continuous (fun t => circleLiftDefectJet (h t) (hh t) (hlift t) n) := by
  apply continuous_periodicCircleJet_family
  have hc : Continuous (fun p : X × ℝ =>
      iteratedDeriv (n + 1) (h p.1) p.2 - if n = 0 then (1 : ℝ) else 0) :=
    hj.sub continuous_const
  exact hc.congr (fun p =>
    (circleLiftDefectJet_coe_apply_eq (h p.1) (hh p.1) (hlift p.1) n p.2).symm.trans
      (circleLiftDefectJet_coe_apply (h p.1) (hh p.1) (hlift p.1) n p.2))

variable {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

include hG hperiod hΘ hinit hflow

/-- Actual circle jets of the derivative defect on the original interval. -/
def circleFlowDefectJet (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  if ht : t ∈ Icc a b then
    circleLiftDefectJet (fun θ => Θ (t, θ))
      (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
      (circleFlow_lift_add hG hperiod hΘ hinit hflow ht) n
  else 0

theorem circleFlowDefectJet_eq {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) :
    circleFlowDefectJet hG hperiod hΘ hinit hflow t n =
      circleLiftDefectJet (fun θ => Θ (t, θ))
        (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
        (circleFlow_lift_add hG hperiod hΘ hinit hflow ht) n := by
  simp only [circleFlowDefectJet, dif_pos ht]

theorem circleFlowDefectJet_coe_apply {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    circleFlowDefectJet hG hperiod hΘ hinit hflow t n (θ : AddCircle P) =
      iteratedDeriv (n + 1) (fun η => Θ (t, η)) θ - if n = 0 then 1 else 0 := by
  rw [circleFlowDefectJet_eq hG hperiod hΘ hinit hflow ht]
  exact circleLiftDefectJet_coe_apply_eq _ _ _ _ _

theorem circleFlowDefectJet_hasDerivAt {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ => circleFlowDefectJet hG hperiod hΘ hinit hflow t n (η : AddCircle P))
      (circleFlowDefectJet hG hperiod hΘ hinit hflow t (n + 1) (θ : AddCircle P)) θ := by
  simp only [circleFlowDefectJet_eq hG hperiod hΘ hinit hflow ht]
  exact circleLiftDefectJet_hasDerivAt _ _ _ _ _

theorem continuousOn_circleFlowDefectJet (n : ℕ) :
    ContinuousOn (fun t => circleFlowDefectJet hG hperiod hΘ hinit hflow t n) (Icc a b) := by
  have hj : Continuous (fun p : Icc a b × ℝ =>
      iteratedDeriv (n + 1) (fun η => Θ (p.1, η)) p.2) :=
    (circleFlow_continuousOn_angularJet hG hP.out hperiod hΘ hinit hflow (n + 1)).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.property, mem_univ p.2⟩)
  have hc := continuous_circleLiftDefectJet_family
    (fun t : Icc a b => fun θ => Θ (t, θ))
    (fun t => circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow t.property)
    (fun t => circleFlow_lift_add hG hperiod hΘ hinit hflow t.property) n hj
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hc.congr (fun t => (circleFlowDefectJet_eq hG hperiod hΘ hinit hflow t.property n).symm)

theorem continuousOn_circleFlowDefectSobolevNorm (s : ℕ) :
    ContinuousOn (fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0)) (Icc a b) :=
  continuousOn_circleRealSobolevNorm_of_derivatives
    (circleFlowDefectJet hG hperiod hΘ hinit hflow)
    (fun t ht => circleFlowDefectJet_hasDerivAt hG hperiod hΘ hinit hflow ht) s
    (continuousOn_circleFlowDefectJet hG hperiod hΘ hinit hflow 0)
    (continuousOn_circleFlowDefectJet hG hperiod hΘ hinit hflow s)

theorem circleFlow_composedSpeed_periodic {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (fun θ => G (t, Θ (t, θ))) P := by
  intro θ
  rw [circleFlow_lift_add hG hperiod hΘ hinit hflow ht θ, hperiod t]

theorem circleFlow_contDiff_composedSpeed_angle {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => G (t, Θ (t, θ))) :=
  (hG.comp (contDiff_const.prodMk contDiff_id)).comp
    (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)

/-- Actual circle jets of the speed composed with the supplied flow. -/
def circleFlowComposedSpeedJet (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  if ht : t ∈ Icc a b then
    periodicCircleJet (fun θ => G (t, Θ (t, θ)))
      (circleFlow_composedSpeed_periodic hG hperiod hΘ hinit hflow ht)
      (circleFlow_contDiff_composedSpeed_angle hG hperiod hΘ hinit hflow ht) n
  else 0

theorem circleFlowComposedSpeedJet_eq {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) :
    circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t n =
      periodicCircleJet (fun θ => G (t, Θ (t, θ)))
        (circleFlow_composedSpeed_periodic hG hperiod hΘ hinit hflow ht)
        (circleFlow_contDiff_composedSpeed_angle hG hperiod hΘ hinit hflow ht) n := by
  simp only [circleFlowComposedSpeedJet, dif_pos ht]

theorem circleFlowComposedSpeedJet_coe_apply {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t n (θ : AddCircle P) =
      iteratedDeriv n (fun η => G (t, Θ (t, η))) θ := by
  rw [circleFlowComposedSpeedJet_eq hG hperiod hΘ hinit hflow ht]
  exact periodicCircleJet_coe_apply _ _ _ _ _

theorem circleFlowComposedSpeedJet_hasDerivAt {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ =>
      circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t n (η : AddCircle P))
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t (n + 1) (θ : AddCircle P)) θ := by
  simp only [circleFlowComposedSpeedJet_eq hG hperiod hΘ hinit hflow ht]
  exact periodicCircleJet_hasDerivAt _ _ _ _ _

theorem continuousOn_circleFlowComposedSpeedJet (n : ℕ) :
    ContinuousOn (fun t => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t n)
      (Icc a b) := by
  have hj : Continuous (fun p : Icc a b × ℝ =>
      iteratedDeriv n (fun η => G (p.1, Θ (p.1, η))) p.2) :=
    (circleFlow_continuousOn_composedAngularJet hG hP.out hperiod hΘ hinit hflow hG n).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.property, mem_univ p.2⟩)
  have hc := continuous_periodicCircleJet_family
    (fun t : Icc a b => fun θ => G (t, Θ (t, θ)))
    (fun t => circleFlow_composedSpeed_periodic hG hperiod hΘ hinit hflow t.property)
    (fun t => circleFlow_contDiff_composedSpeed_angle hG hperiod hΘ hinit hflow t.property) n hj
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hc.congr (fun t => (circleFlowComposedSpeedJet_eq hG hperiod hΘ hinit hflow t.property n).symm)

end ContinuousFlexibility.Analysis
