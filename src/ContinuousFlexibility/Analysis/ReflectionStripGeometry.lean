import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Topology.Order.IntermediateValue

/-!
# Reflection and angular fibers on a genuine radial strip

A chart which commutes with angular translation by `π`, respects reflection,
and has an inverse preserves the open angular strip `(0, π)`.  This identifies
the actual domains needed for the ordinary planar change-of-variables theorem;
there is no implicit change of fundamental domain in the source pairing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

private theorem mapsTo_openInterval_of_boundary_fibers
    {P : ℝ} (hP : 0 < P) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 P)) (hf0 : f 0 = 0) (hfP : f P = P)
    (hzero : ∀ t ∈ Icc 0 P, f t = 0 → t = 0)
    (hperiod : ∀ t ∈ Icc 0 P, f t = P → t = P) :
    MapsTo f (Ioo 0 P) (Ioo 0 P) := by
  intro t ht
  constructor
  · by_contra h
    have hft : f t ≤ 0 := le_of_not_gt h
    have hcont : ContinuousOn f (Icc t P) :=
      hf.mono (Icc_subset_Icc ht.1.le le_rfl)
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.2.le hcont
      (show (0 : ℝ) ∈ Icc (f t) (f P) from ⟨hft, by rw [hfP]; exact hP.le⟩)
    have hs0 := hzero s ⟨ht.1.le.trans hs.1, hs.2⟩ hfs
    linarith [hs.1, ht.1]
  · by_contra h
    have hft : P ≤ f t := le_of_not_gt h
    have hcont : ContinuousOn f (Icc 0 t) :=
      hf.mono (Icc_subset_Icc le_rfl ht.2.le)
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.1.le hcont
      (show P ∈ Icc (f 0) (f t) from ⟨by rw [hf0]; exact hP.le, hft⟩)
    have hsP := hperiod s ⟨hs.1, hs.2.trans ht.2.le⟩ hfs
    linarith [hs.2, ht.2]

/-- Reflection and injectivity identify the preimage of the angular axis. -/
theorem chart_angle_eq_zero_of_reflection
    {a b : ℝ} {F : PolarPoint → PolarPoint}
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ (univ : Set ℝ))
    (hangle : (F p).2 = 0) : p.2 = 0 := by
  have hp' : (p.1, -p.2) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hF : F (p.1, -p.2) = F p := by
    rw [hreflect p hp]
    apply Prod.ext
    · rfl
    · simp only [hangle, neg_zero]
  have h := congrArg Prod.snd (hinj hp' hp hF)
  change -p.2 = p.2 at h
  linarith

/-- The equivariance of a chart passes to its actual inverse. -/
theorem inverseChart_periodic_of_chart_periodic
    {a b c d P : ℝ} {F G : PolarPoint → PolarPoint}
    (hG : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hFG : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), F (G p) = p)
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    {p : PolarPoint} (hp : p ∈ Ioo c d ×ˢ (univ : Set ℝ)) :
    G (p + (0, P)) = G p + (0, P) := by
  have hGp := hG hp
  have hGp' : G p + (0, P) ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
    exact ⟨by simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hGp.1, mem_univ _⟩
  have h := hperiod (G p) hGp
  rw [hFG p hp] at h
  calc
    G (p + (0, P)) = G (F (G p + (0, P))) := congrArg G h.symm
    _ = G p + (0, P) := hGF _ hGp'

/-- A continuous equivariant reflection-preserving injection maps the open
fundamental angular strip into itself. -/
theorem chart_mapsTo_openAngularStrip
    {a b c d P : ℝ} {F : PolarPoint → PolarPoint} (hP : 0 < P)
    (hF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hcont : ContinuousOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2)) :
    MapsTo F (Ioo a b ×ˢ Ioo 0 P) (Ioo c d ×ˢ Ioo 0 P) := by
  intro p hp
  have hpfull : p ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  refine ⟨(hF hpfull).1, ?_⟩
  let f : ℝ → ℝ := fun t => (F (p.1, t)).2
  have hpath : Continuous (fun t : ℝ => (p.1, t)) := continuous_const.prodMk continuous_id
  have hf : ContinuousOn f (Icc 0 P) :=
    hcont.snd.comp hpath.continuousOn (fun t _ => ⟨hp.1, mem_univ _⟩)
  have hf0 : f 0 = 0 := by
    have h := congrArg Prod.snd (hreflect (p.1, 0) ⟨hp.1, mem_univ _⟩)
    simp only [neg_zero] at h
    change f 0 = -f 0 at h
    linarith
  have htranslate (t : ℝ) : f (t + P) = f t + P := by
    have h := congrArg Prod.snd (hperiod (p.1, t) ⟨hp.1, mem_univ _⟩)
    simpa only [f, Prod.mk_add_mk, Prod.snd_add, add_zero] using h
  have hfP : f P = P := by simpa only [zero_add, hf0] using htranslate 0
  have hzero : ∀ t ∈ Icc 0 P, f t = 0 → t = 0 := by
    intro t _ ht
    exact chart_angle_eq_zero_of_reflection (p := (p.1, t))
      hinj hreflect ⟨hp.1, mem_univ _⟩ ht
  have hPfiber : ∀ t ∈ Icc 0 P, f t = P → t = P := by
    intro t _ ht
    have heq : f (t - P) = 0 := by
      have heq := htranslate (t - P)
      rw [sub_add_cancel, ht] at heq
      linarith
    have hz : t - P = 0 :=
      chart_angle_eq_zero_of_reflection (p := (p.1, t - P))
        hinj hreflect ⟨hp.1, mem_univ _⟩ heq
    linarith
  exact mapsTo_openInterval_of_boundary_fibers hP hf hf0 hfP hzero hPfiber hp.2

end ContinuousFlexibility.Analysis
