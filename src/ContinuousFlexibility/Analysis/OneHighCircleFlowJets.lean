import ContinuousFlexibility.Analysis.OneHighCircleFlowTimeChange
import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Continuous actual angular jets at the time endpoints

The flat compact time change is a continuous surjection from a compact
interval. Its product with the angle identity is a proper quotient map.
Consequently continuity of the actual angular jets of the smooth
time-changed family descends to the original closed time strip. This
avoids differentiating an inverse of the flat time change.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Topology

/-- Continuity descends from a compact, surjective reparametrization of
the time coordinate, even though the angle coordinate is noncompact. -/
theorem continuousOn_of_compact_time_reparam {E : Type*} [TopologicalSpace E]
    {F : PolarPoint → E} {τ : ℝ → ℝ} {a b : ℝ}
    (hτ : Continuous τ)
    (hτrange : ∀ s ∈ Icc (0 : ℝ) 1, τ s ∈ Icc a b)
    (hτsurj : SurjOn τ (Icc (0 : ℝ) 1) (Icc a b))
    (hcomp : Continuous (fun p : PolarPoint => F (τ p.1, p.2))) :
    ContinuousOn F (Icc a b ×ˢ (univ : Set ℝ)) := by
  let σ : Icc (0 : ℝ) 1 → Icc a b := fun s => ⟨τ s, hτrange s s.property⟩
  have hσ : Continuous σ :=
    (hτ.comp continuous_subtype_val).subtype_mk (fun s => hτrange s s.property)
  have hsurj : Function.Surjective σ := by
    intro t
    obtain ⟨s, hs, he⟩ := hτsurj t.property
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩
  have hproper : IsProperMap (Prod.map σ (id : ℝ → ℝ)) :=
    hσ.isProperMap.prodMap isProperMap_id
  have hquot : IsQuotientMap (Prod.map σ (id : ℝ → ℝ)) :=
    hproper.isClosedMap.isQuotientMap (hσ.prodMap continuous_id)
      (hsurj.prodMap Function.surjective_id)
  have hF : Continuous (fun p : Icc a b × ℝ => F (p.1, p.2)) := by
    apply hquot.continuous_iff.mpr
    exact hcomp.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hrestriction : Continuous
      (fun p : (Icc a b ×ˢ (univ : Set ℝ)) =>
        ((⟨p.val.1, p.property.1⟩ : Icc a b), p.val.2)) :=
    ((continuous_subtype_val.fst).subtype_mk (fun p => p.property.1)).prodMk
      continuous_subtype_val.snd
  exact continuousOn_iff_continuous_domRestrict.mpr (hF.comp hrestriction)

/-- Every actual angular jet of the supplied classical periodic flow is
jointly continuous on the entire closed time strip. -/
theorem circleFlow_continuousOn_angularJet {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (n : ℕ) :
    ContinuousOn (fun p : PolarPoint => iteratedDeriv n (fun η => Θ (p.1, η)) p.2)
      (Icc a b ×ˢ (univ : Set ℝ)) := by
  by_cases hab : a ≤ b
  · have hsmooth := contDiff_circleFlow_timeChange hG hP hperiod hΘ hinit hflow
      (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
      (circleFlowCompactTime_mem hab)
    have hjet : Continuous (fun p : PolarPoint =>
        iteratedDeriv n (fun η => Θ (circleFlowCompactTime a b p.1, η)) p.2) := by
      have hc := (contDiffOn_univ.mp
        (Statements.contDiffOn_mixedDerivative isOpen_univ hsmooth.contDiffOn 0 n)).continuous
      simpa only [Statements.mixedDerivative, iteratedDeriv_zero] using hc
    exact continuousOn_of_compact_time_reparam
      (contDiff_circleFlowCompactTime a b).continuous
      (fun s _ => circleFlowCompactTime_mem hab s)
      (circleFlowCompactTime_surjOn a b) hjet
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), empty_prod]
    exact continuousOn_empty

end ContinuousFlexibility.Analysis
