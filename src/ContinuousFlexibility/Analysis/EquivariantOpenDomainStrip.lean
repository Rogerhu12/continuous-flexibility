module

public import ContinuousFlexibility.Analysis.PeriodicLiftAxisIntervals
public import ContinuousFlexibility.Analysis.ReflectionStripGeometry

/-!
# A fundamental angular strip for a general physical domain

The inverse chart has a full fixed canonical strip as its domain. Its
angular component preserves the fundamental interval by its genuine
axis fibers and bounded periodic displacement. Thus no path at a fixed
physical radius, and no radial-graph assumption on a moving cut, is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- An injective continuous reflection-preserving equivariant map on a
full source strip preserves the fundamental angular interval in both
directions. Its image need not be a radial strip. -/
theorem chart_angle_mem_Ioo_iff
    {A : Set ℝ} {P : ℝ} {G : PolarPoint → PolarPoint} (hP : P ≠ 0)
    (hinj : InjOn G (A ×ˢ (univ : Set ℝ)))
    (hcont : ContinuousOn G (A ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ A ×ˢ (univ : Set ℝ), G (p + (0, P)) = G p + (0, P))
    (hreflect : ∀ p ∈ A ×ˢ (univ : Set ℝ),
      G (p.1, -p.2) = ((G p).1, -(G p).2))
    {p : PolarPoint} (hp : p ∈ A ×ˢ (univ : Set ℝ)) :
    (G p).2 ∈ Ioo 0 P ↔ p.2 ∈ Ioo 0 P := by
  let f : ℝ → ℝ := fun θ => (G (p.1, θ)).2
  have hf : Continuous f := by
    rw [← continuousOn_univ]
    exact hcont.snd.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ _ => ⟨hp.1, mem_univ _⟩)
  have hfp (θ : ℝ) : f (θ + P) = f θ + P := by
    simpa only [f, Prod.mk_add_mk, add_zero, Prod.snd_add] using
      congrArg Prod.snd (hperiod (p.1, θ) ⟨hp.1, mem_univ _⟩)
  have hf0 : f 0 = 0 := by
    have he := congrArg Prod.snd (hreflect (p.1, 0) ⟨hp.1, mem_univ _⟩)
    simp only [neg_zero] at he
    change f 0 = -f 0 at he
    linarith
  have hfP : f P = P := by simpa only [zero_add, hf0] using hfp 0
  have hzero (θ : ℝ) (hθ : f θ = 0) : θ = 0 :=
    chart_angle_eq_zero_of_reflection hinj hreflect
      (p := (p.1, θ)) ⟨hp.1, mem_univ _⟩ hθ
  have hPfiber (θ : ℝ) (hθ : f θ = P) : θ = P := by
    have he := hfp (θ - P)
    rw [sub_add_cancel, hθ] at he
    have h0 : f (θ - P) = 0 := by linarith
    have ht := hzero (θ - P) h0
    linarith
  exact mem_Ioo_periodicLift_iff hP hf hfp hf0 hfP hzero hPfiber

/-- Domain invariance passes the forward translation identity to the
actual inverse, with no rectangularity requirement on the physical set. -/
theorem inverseChart_periodic_on_invariant_domain
    {Ω : Set PolarPoint} {a b P : ℝ} {F G : PolarPoint → PolarPoint}
    (hΩ : ∀ p ∈ Ω, p + (0, P) ∈ Ω)
    (hG : MapsTo G (Ioo a b ×ˢ (univ : Set ℝ)) Ω)
    (hGF : ∀ p ∈ Ω, G (F p) = p)
    (hFG : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (G p) = p)
    (hperiod : ∀ p ∈ Ω, F (p + (0, P)) = F p + (0, P))
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ (univ : Set ℝ)) :
    G (p + (0, P)) = G p + (0, P) := by
  have he := hperiod (G p) (hG hp)
  rw [hFG p hp] at he
  calc
    G (p + (0, P)) = G (F (G p + (0, P))) := congrArg G he.symm
    _ = G p + (0, P) := hGF _ (hΩ _ (hG hp))

theorem inverseChart_reflect_on_invariant_domain
    {Ω : Set PolarPoint} {a b : ℝ} {F G : PolarPoint → PolarPoint}
    (hΩ : ∀ p ∈ Ω, (p.1, -p.2) ∈ Ω)
    (hG : MapsTo G (Ioo a b ×ˢ (univ : Set ℝ)) Ω)
    (hGF : ∀ p ∈ Ω, G (F p) = p)
    (hFG : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (G p) = p)
    (hreflect : ∀ p ∈ Ω, F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ (univ : Set ℝ)) :
    G (p.1, -p.2) = ((G p).1, -(G p).2) := by
  have he := hreflect (G p) (hG hp)
  rw [hFG p hp] at he
  calc
    G (p.1, -p.2) = G (F ((G p).1, -(G p).2)) := congrArg G he.symm
    _ = ((G p).1, -(G p).2) := hGF _ (hΩ _ (hG hp))

/-- The actual fundamental-strip image follows from the inverse on the
fixed canonical strip, even for a curved physical domain. -/
theorem equivariantChart_image_openAngularStrip
    {Ω : Set PolarPoint} {a b P : ℝ} {F G : PolarPoint → PolarPoint}
    (hP : P ≠ 0)
    (hF : MapsTo F Ω (Ioo a b ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo a b ×ˢ (univ : Set ℝ)) Ω)
    (hGF : ∀ p ∈ Ω, G (F p) = p)
    (hFG : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (G p) = p)
    (hcont : ContinuousOn G (Ioo a b ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (p + (0, P)) = G p + (0, P))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      G (p.1, -p.2) = ((G p).1, -(G p).2)) :
    F '' (Ω ∩ (univ ×ˢ Ioo (0 : ℝ) P)) =
      (Ioo a b ×ˢ (univ : Set ℝ)) ∩ (univ ×ˢ Ioo (0 : ℝ) P) := by
  have hinj : InjOn G (Ioo a b ×ˢ (univ : Set ℝ)) := by
    intro p hp q hq he
    calc
      p = F (G p) := (hFG p hp).symm
      _ = F (G q) := congrArg F he
      _ = q := hFG q hq
  have hang := fun p hp => chart_angle_mem_Ioo_iff hP hinj hcont hperiod hreflect (p := p) hp
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨hF hp.1, ⟨mem_univ _, ?_⟩⟩
    apply (hang (F p) (hF hp.1)).mp
    simpa only [hGF p hp.1] using hp.2.2
  · intro p hp
    refine ⟨G p, ⟨hG hp.1, ⟨mem_univ _, (hang p hp.1).mpr hp.2.2⟩⟩, hFG p hp.1⟩

end ContinuousFlexibility.Analysis
