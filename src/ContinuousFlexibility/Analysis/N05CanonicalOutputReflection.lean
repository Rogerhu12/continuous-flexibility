import ContinuousFlexibility.Analysis.N05CanonicalInverseDefinition
import ContinuousFlexibility.Analysis.N05CanonicalTests

/-!
# Reflection of the actual canonical output

The physical output is even and π-periodic. The genuine N04 inverse chart
and height transfer these two identities to reflection about the midpoint
of the canonical half-period. Almost-everywhere representatives then give
the exact reflection equation in the canonical L² space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- Physical parity and periodicity transfer through the actual chart;
no pointwise property of an arbitrarily chosen L² representative is used. -/
theorem n05_canonicalHeight_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m f (p.1, Real.pi - p.2) =
      canonicalHeight S K z m f p := by
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _, hreflect, hinverse, _⟩
  obtain ⟨_, hΨ, hleft, hright, _, _, _, hgeometry⟩ := hcharts z hz hs m
  have hshift (q : PolarPoint) (hq : q ∈ canonicalOpen S K m) :
      K.inverseChart z m (q + (0, Real.pi)) =
        K.inverseChart z m q + (0, Real.pi) := by
    have hx := hΨ hq
    have hxshift : K.inverseChart z m q + (0, Real.pi) ∈ physicalPieceOpen S K m := by
      exact ⟨by simpa only [Prod.fst_add, add_zero] using hx.1, mem_univ _⟩
    have he : K.chart z m (K.inverseChart z m q + (0, Real.pi)) =
        q + (0, Real.pi) := by
      rw [(hgeometry _ hx).2.2.1, hright q hq]
    rw [← he]
    exact hleft _ hxshift
  have hpneg : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hx := hΨ hp
  have hxneg : ((K.inverseChart z m p).1, -(K.inverseChart z m p).2) ∈
      physicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  have he : (p.1, Real.pi - p.2) = (p.1, -p.2) + ((0, Real.pi) : PolarPoint) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  have hi : K.inverseChart z m (p.1, Real.pi - p.2) =
      ((K.inverseChart z m p).1, -(K.inverseChart z m p).2) + (0, Real.pi) := by
    rw [he, hshift _ hpneg, hinverse z hz hs m p hp]
  unfold canonicalHeight
  rw [hi, hf, (hgeometry _ hxneg).2.2.2, heven,
    (hreflect z hz hs m (K.inverseChart z m p) hx).2.1]

/-- The genuine L² class of a canonical height satisfies the frozen
half-period reflection equation. -/
theorem n05_canonicalL2_reflection_of_height_rep
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (m : ℕ) {u : CanonicalL2 S K m}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m f) :
    n05CanonicalReflection S K m u = u := by
  apply (n05CanonicalReflection_fixed_iff S K m u).mpr
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp hu
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hu, hr, hmem] with p hp hr hpU
  exact hr.trans ((n05_canonicalHeight_reflection h04 hz hs hf heven m
    (show p ∈ canonicalOpen S K m from ⟨hpU.1, mem_univ _⟩)).trans hp.symm)

/-- Every coordinate of the same fixed global inverse is an even
canonical L² class on each actual source volume level. -/
theorem n05CanonicalGlobalInverse_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ M0 M1 : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
    {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γw M0 M1 G)
    (t : ℝ) (s : ℕ) (v : V.level γ t s) (m : ℕ) :
    n05CanonicalReflection S K m
        ((n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 m) =
      (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 m := by
  obtain ⟨hrep, hgraph⟩ :=
    n05CanonicalGlobalInverse_represents hD hT hS h hcoordinates hV hγw hgap hG t s v
  obtain ⟨a, ha⟩ := hgraph.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  apply n05_canonicalL2_reflection_of_height_rep h.2.2.2.2 hz hs ?_ ?_ m (hrep.1 m)
  · intro p
    dsimp only
    rw [ha.2.2.1 p]
    simp only [Prod.fst_add, add_zero]
  · intro r θ
    dsimp only
    rw [ha.2.2.2 r θ]

end ContinuousFlexibility.Statements
