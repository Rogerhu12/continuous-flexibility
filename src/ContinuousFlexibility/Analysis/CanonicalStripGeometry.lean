import ContinuousFlexibility.Blueprint.CanonicalParts
import Mathlib.Topology.Order.IntermediateValue

/-!
# The fundamental angular strip of a canonical chart

On a genuine source cylinder, angular translation, reflection, and
injectivity characterize the open angular strip `(0, π)` in both directions.
For a state-dependent physical piece this argument is applied to the inverse
chart on the fixed canonical cylinder. Thus no physical radial fiber is
assumed to remain inside the piece. This identifies the actual domains for
the ordinary planar change-of-variables theorem and the source pairing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

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

/-- Continuity and the unique boundary fibers also exclude points outside
the fundamental interval. The two IVT applications stay in the connected
half-lines outside its boundary, so no integer period reduction is needed. -/
private theorem mem_openInterval_iff_of_periodic_boundary_fibers
    {P : ℝ} (hP : 0 < P) {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : f 0 = 0)
    (htranslate : ∀ t, f (t + P) = f t + P)
    (hzero : ∀ t, f t = 0 → t = 0) {t : ℝ} :
    f t ∈ Ioo 0 P ↔ t ∈ Ioo 0 P := by
  have hfP : f P = P := by
    simpa only [zero_add, hf0] using htranslate 0
  have hPfiber : ∀ s, f s = P → s = P := by
    intro s hs
    have h := htranslate (s - P)
    rw [sub_add_cancel, hs] at h
    have hz : f (s - P) = 0 := by linarith
    linarith [hzero (s - P) hz]
  constructor
  · intro ht
    constructor
    · by_contra h
      have hne : t ≠ 0 := by
        intro he
        have hpos := ht.1
        rw [he, hf0] at hpos
        exact (lt_irrefl 0) hpos
      have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt h) hne
      have hfnegP : f (-P) = -P := by
        have hneg := htranslate (-P)
        rw [neg_add_cancel, hf0] at hneg
        linarith
      obtain ⟨s, hs, hfs⟩ := isPreconnected_Iio.intermediate_value
        (show -P ∈ Iio (0 : ℝ) from neg_lt_zero.mpr hP)
        (show t ∈ Iio (0 : ℝ) from htneg) hf.continuousOn
        (show (0 : ℝ) ∈ Icc (f (-P)) (f t) from
          ⟨by rw [hfnegP]; linarith, ht.1.le⟩)
      exact (ne_of_lt hs) (hzero s hfs)
    · by_contra h
      have hne : t ≠ P := by
        intro he
        have hlt := ht.2
        rw [he, hfP] at hlt
        exact (lt_irrefl P) hlt
      have htgt : P < t := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      have hfTwoP : f (P + P) = P + P := by rw [htranslate, hfP]
      obtain ⟨s, hs, hfs⟩ := isPreconnected_Ioi.intermediate_value
        (show t ∈ Ioi P from htgt)
        (show P + P ∈ Ioi P from lt_add_of_pos_right P hP) hf.continuousOn
        (show P ∈ Icc (f t) (f (P + P)) from
          ⟨ht.2.le, by rw [hfTwoP]; linarith⟩)
      exact (ne_of_gt hs) (hPfiber s hfs)
  · intro ht
    exact mapsTo_openInterval_of_boundary_fibers hP hf.continuousOn hf0 hfP
      (fun s _ => hzero s) (fun s _ => hPfiber s) ht

/-- Reflection and injectivity identify the preimage of the angular axis. -/
theorem chart_angle_eq_zero_of_reflection
    {A : Set ℝ} {F : PolarPoint → PolarPoint}
    (hinj : InjOn F (A ×ˢ (univ : Set ℝ)))
    (hreflect : ∀ p ∈ A ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ A ×ˢ (univ : Set ℝ))
    (hangle : (F p).2 = 0) : p.2 = 0 := by
  have hp' : (p.1, -p.2) ∈ A ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hF : F (p.1, -p.2) = F p := by
    rw [hreflect p hp]
    apply Prod.ext
    · rfl
    · simp only [hangle, neg_zero]
  have h := congrArg Prod.snd (hinj hp' hp hF)
  change -p.2 = p.2 at h
  linarith

/-- Equivariance passes to an actual inverse on an arbitrary physical
domain invariant under angular translation. -/
theorem inverseChart_periodic_of_chart_periodic_on
    {Ω U : Set PolarPoint} {P : ℝ} {F G : PolarPoint → PolarPoint}
    (hG : MapsTo G U Ω)
    (hshift : ∀ p ∈ Ω, p + (0, P) ∈ Ω)
    (hGF : ∀ p ∈ Ω, G (F p) = p)
    (hFG : ∀ p ∈ U, F (G p) = p)
    (hperiod : ∀ p ∈ Ω, F (p + (0, P)) = F p + (0, P))
    {p : PolarPoint} (hp : p ∈ U) :
    G (p + (0, P)) = G p + (0, P) := by
  have hGp := hG hp
  have h := hperiod (G p) hGp
  rw [hFG p hp] at h
  calc
    G (p + (0, P)) = G (F (G p + (0, P))) := congrArg G h.symm
    _ = G p + (0, P) := hGF _ (hshift _ hGp)

/-- The original strip-domain specialization of inverse equivariance. -/
theorem inverseChart_periodic_of_chart_periodic
    {a b c d P : ℝ} {F G : PolarPoint → PolarPoint}
    (hG : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hFG : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), F (G p) = p)
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    {p : PolarPoint} (hp : p ∈ Ioo c d ×ˢ (univ : Set ℝ)) :
    G (p + (0, P)) = G p + (0, P) := by
  apply inverseChart_periodic_of_chart_periodic_on hG ?_ hGF hFG hperiod hp
  intro q hq
  exact ⟨by simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hq.1, mem_univ _⟩

/-- The angular interval is characterized in both directions on a genuine
source cylinder. The image need not be a radial strip. -/
theorem chart_angle_mem_openInterval_iff
    {A : Set ℝ} {P : ℝ} {F : PolarPoint → PolarPoint} (hP : 0 < P)
    (hinj : InjOn F (A ×ˢ (univ : Set ℝ)))
    (hcont : ContinuousOn F (A ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ A ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    (hreflect : ∀ p ∈ A ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ A ×ˢ (univ : Set ℝ)) :
    (F p).2 ∈ Ioo 0 P ↔ p.2 ∈ Ioo 0 P := by
  let f : ℝ → ℝ := fun t => (F (p.1, t)).2
  have hpath : Continuous (fun t : ℝ => (p.1, t)) := continuous_const.prodMk continuous_id
  have hf : Continuous f :=
    hcont.snd.comp_continuous hpath (fun _ => ⟨hp.1, mem_univ _⟩)
  have hf0 : f 0 = 0 := by
    have h := congrArg Prod.snd (hreflect (p.1, 0) ⟨hp.1, mem_univ _⟩)
    simp only [neg_zero] at h
    change f 0 = -f 0 at h
    linarith
  have htranslate (t : ℝ) : f (t + P) = f t + P := by
    have h := congrArg Prod.snd (hperiod (p.1, t) ⟨hp.1, mem_univ _⟩)
    simpa only [f, Prod.mk_add_mk, Prod.snd_add, add_zero] using h
  have hzero : ∀ t, f t = 0 → t = 0 := by
    intro t ht
    exact chart_angle_eq_zero_of_reflection (p := (p.1, t))
      hinj hreflect ⟨hp.1, mem_univ _⟩ ht
  exact mem_openInterval_iff_of_periodic_boundary_fibers hP hf hf0 htranslate hzero

/-- A genuine source cylinder may map into an arbitrary physical domain. -/
theorem chart_mapsTo_openAngularStrip_target
    {a b P : ℝ} {Ω : Set PolarPoint} {F : PolarPoint → PolarPoint} (hP : 0 < P)
    (hF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) Ω)
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hcont : ContinuousOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2)) :
    MapsTo F (Ioo a b ×ˢ Ioo 0 P) (Ω ∩ (univ ×ˢ Ioo 0 P)) := by
  intro p hp
  have hpfull : p ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  exact ⟨hF hpfull, mem_univ _,
    (chart_angle_mem_openInterval_iff hP hinj hcont hperiod hreflect hpfull).mpr hp.2⟩

/-- The strip-to-strip specialization retains its original interface. -/
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
  have h := chart_mapsTo_openAngularStrip_target hP hF hinj hcont hperiod hreflect hp
  exact ⟨h.1.1, h.2.2⟩

/-- An actual canonical chart is injective on its whole physical piece. -/
theorem canonicalChart_injOn
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    InjOn (K.chart z m) (physicalPieceOpen S K z m) := by
  have hcharts := hK.charts z hz hsector m
  intro p hp q hq heq
  calc
    p = K.inverseChart z m (K.chart z m p) := (hcharts.2.2.1 p hp).symm
    _ = K.inverseChart z m (K.chart z m q) := congrArg (K.inverseChart z m) heq
    _ = q := hcharts.2.2.1 q hq

/-- The physical and canonical open fundamental angular strips have exactly
the same image under the specified canonical chart. -/
theorem canonicalChart_image_openStrip
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    K.chart z m '' (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) =
      canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) := by
  have hcharts := hK.charts z hz hsector m
  have hdomains := hK.domains z hz hsector m
  have hinverseReflect := hK.inverseReflection z hz hsector m
  have hFperiod : ∀ p ∈ physicalPieceOpen S K z m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).2.2.1
  have hGperiod : ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
    intro p hp
    exact inverseChart_periodic_of_chart_periodic_on hcharts.2.1
      (fun q hq => (hdomains.2.2.2.1 q).mpr hq) hcharts.2.2.1
      hcharts.2.2.2.1 hFperiod hp
  have hGinj : InjOn (K.inverseChart z m) (canonicalOpen S K m) := by
    intro p hp q hq heq
    calc
      p = K.chart z m (K.inverseChart z m p) := (hcharts.2.2.2.1 p hp).symm
      _ = K.chart z m (K.inverseChart z m q) := congrArg (K.chart z m) heq
      _ = q := hcharts.2.2.2.1 q hq
  have hGangle : ∀ p ∈ canonicalOpen S K m,
      (K.inverseChart z m p).2 ∈ Ioo (0 : ℝ) Real.pi ↔
        p.2 ∈ Ioo (0 : ℝ) Real.pi := by
    intro p hp
    exact chart_angle_mem_openInterval_iff Real.pi_pos hGinj
      hcharts.2.2.2.2.2.1.continuousOn hGperiod hinverseReflect hp
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    have hqchart := hcharts.1 hq.1
    refine ⟨hqchart, mem_univ _, (hGangle _ hqchart).mp ?_⟩
    rw [hcharts.2.2.1 q hq.1]
    exact hq.2.2
  · intro p hp
    refine ⟨K.inverseChart z m p,
      ⟨hcharts.2.1 hp.1, mem_univ _, (hGangle p hp.1).mpr hp.2.2⟩, ?_⟩
    exact hcharts.2.2.2.1 p hp.1

end ContinuousFlexibility.Analysis
