module

public import ContinuousFlexibility.Analysis.ParametricSpatialIntegralJets
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Spatial jets on a closed time interval

A smooth compact time reparametrization supplies genuine joint
continuity of the spatial jets at both time endpoints. Proper quotient
maps descend that continuity without differentiating the inverse time
map. A continuous time clamp then permits the already proved actual
derivative-under-integral theorem on the original interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Topology MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem continuousOn_of_compact_parameter_time_reparam
    {Q E : Type*} [TopologicalSpace Q] [TopologicalSpace E]
    {f : Q × ℝ → E} {τ : ℝ → ℝ} {a b : ℝ}
    (hτ : Continuous τ)
    (hτrange : ∀ s ∈ Icc (0 : ℝ) 1, τ s ∈ Icc a b)
    (hτsurj : SurjOn τ (Icc (0 : ℝ) 1) (Icc a b))
    (hcomp : Continuous (fun z : Q × ℝ => f (z.1, τ z.2))) :
    ContinuousOn f (univ ×ˢ Icc a b) := by
  let σ : Icc (0 : ℝ) 1 → Icc a b := fun s => ⟨τ s, hτrange s s.property⟩
  have hσ : Continuous σ :=
    (hτ.comp continuous_subtype_val).subtype_mk (fun s => hτrange s s.property)
  have hsurj : Function.Surjective σ := by
    intro t
    obtain ⟨s, hs, he⟩ := hτsurj t.property
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩
  have hproper : IsProperMap (Prod.map (id : Q → Q) σ) :=
    isProperMap_id.prodMap hσ.isProperMap
  have hquot : IsQuotientMap (Prod.map (id : Q → Q) σ) :=
    hproper.isClosedMap.isQuotientMap (continuous_id.prodMap hσ)
      (Function.surjective_id.prodMap hsurj)
  have hc : Continuous (fun z : Q × Icc a b => f (z.1, z.2)) := by
    apply hquot.continuous_iff.mpr
    exact hcomp.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hrestriction : Continuous
      (fun z : (univ ×ˢ Icc a b : Set (Q × ℝ)) =>
        (z.val.1, (⟨z.val.2, z.property.2⟩ : Icc a b))) :=
    continuous_subtype_val.fst.prodMk
      (continuous_subtype_val.snd.subtype_mk (fun z => z.property.2))
  exact continuousOn_iff_continuous_domRestrict.mpr (hc.comp hrestriction)

variable {Q E : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : Q × ℝ → E} {τ : ℝ → ℝ} {a b : ℝ}

theorem contDiff_spatialSlice_of_timeReparam
    (hτsurj : SurjOn τ (Icc (0 : ℝ) 1) (Icc a b))
    (hf : ContDiff ℝ ∞ (fun z : Q × ℝ => f (z.1, τ z.2)))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun q : Q => f (q, t)) := by
  obtain ⟨s, _, hs⟩ := hτsurj ht
  have hc : ContDiff ℝ ∞ (fun q : Q => f (q, τ s)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  simpa only [hs] using hc

theorem continuousOn_parametricSpatialJet_of_timeReparam
    (hτ : Continuous τ)
    (hτrange : ∀ s ∈ Icc (0 : ℝ) 1, τ s ∈ Icc a b)
    (hτsurj : SurjOn τ (Icc (0 : ℝ) 1) (Icc a b))
    (hf : ContDiff ℝ ∞ (fun z : Q × ℝ => f (z.1, τ z.2))) (n : ℕ) :
    ContinuousOn (parametricSpatialJet f n) (univ ×ˢ Icc a b) := by
  have hjet : Continuous
      (parametricSpatialJet (fun z : Q × ℝ => f (z.1, τ z.2)) n) :=
    (contDiff_parametricSpatialJet hf n).continuous
  have he : parametricSpatialJet (fun z : Q × ℝ => f (z.1, τ z.2)) n =
      (fun z : Q × ℝ => parametricSpatialJet f n (z.1, τ z.2)) := by
    funext z
    rfl
  rw [he] at hjet
  exact continuousOn_of_compact_parameter_time_reparam hτ hτrange hτsurj hjet

variable [FiniteDimensional ℝ Q] [CompleteSpace E]

/-- A compact smooth time reparametrization justifies every actual
spatial derivative under an integral on the original closed interval. -/
theorem parametricIntervalIntegral_closed_contDiff_and_iteratedFDeriv
    (hτ : Continuous τ)
    (hτrange : ∀ s ∈ Icc (0 : ℝ) 1, τ s ∈ Icc a b)
    (hτsurj : SurjOn τ (Icc (0 : ℝ) 1) (Icc a b))
    (hf : ContDiff ℝ ∞ (fun z : Q × ℝ => f (z.1, τ z.2)))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun q : Q => ∫ r in a..t, f (q, r)) ∧
      ∀ n : ℕ, ∀ q : Q,
        iteratedFDeriv ℝ n (fun y : Q => ∫ r in a..t, f (y, r)) q =
          ∫ r in a..t, parametricSpatialJet f n (q, r) := by
  let clamp : ℝ → ℝ := fun r => max a (min r b)
  have hc : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hmem (r : ℝ) : clamp r ∈ Icc a b :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_right _ _)⟩
  have heq (r : ℝ) (hr : r ∈ Icc a b) : clamp r = r := by
    dsimp only [clamp]
    rw [min_eq_left hr.2, max_eq_right hr.1]
  let fc : Q × ℝ → E := fun z => f (z.1, clamp z.2)
  have hfc (r : ℝ) : ContDiff ℝ ∞ (fun q : Q => fc (q, r)) :=
    contDiff_spatialSlice_of_timeReparam hτsurj hf (hmem r)
  have hj (n : ℕ) : Continuous (parametricSpatialJet fc n) := by
    have h := (continuousOn_parametricSpatialJet_of_timeReparam
      hτ hτrange hτsurj hf n).comp_continuous
        (continuous_fst.prodMk (hc.comp continuous_snd))
        (fun z => ⟨mem_univ _, hmem z.2⟩)
    have he : parametricSpatialJet fc n =
        parametricSpatialJet f n ∘ (fun z : Q × ℝ => (z.1, clamp z.2)) := by
      funext z
      rfl
    rw [he]
    exact h
  have hI := parametricIntervalIntegral_contDiff_and_iteratedFDeriv fc hfc hj a t
  have hwithin (r : ℝ) (hr : r ∈ uIcc a t) : r ∈ Icc a b := by
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    exact ⟨hr'.1, hr'.2.trans ht.2⟩
  have hfun : (fun q : Q => ∫ r in a..t, fc (q, r)) =
      fun q : Q => ∫ r in a..t, f (q, r) := by
    funext q
    apply intervalIntegral.integral_congr
    intro r hr
    change f (q, clamp r) = f (q, r)
    rw [heq r (hwithin r hr)]
  rw [hfun] at hI
  refine ⟨hI.1, ?_⟩
  intro n q
  rw [hI.2 n q]
  apply intervalIntegral.integral_congr
  intro r hr
  change iteratedFDeriv ℝ n (fun y : Q => f (y, clamp r)) q =
    iteratedFDeriv ℝ n (fun y : Q => f (y, r)) q
  rw [heq r (hwithin r hr)]

end ContinuousFlexibility.Analysis
