import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import ContinuousFlexibility.Analysis.N06CanonicalProperties
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange

/-!
# Half-period change of variables for the actual current chart

Reflection and equivariance fix the two angular seams. The established
intermediate-value argument for the open angular strip then gives the
actual half-open tile in both directions. The original chart is
therefore a bijection of the measured physical and canonical rectangles,
even when its angular coordinate is not the original angle. All measure
formulas use its genuine Frechet derivative and the frozen Jacobian.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Reflection fixes angle zero, and translation equivariance then
fixes the upper seam. No monotonicity of an angular slice is assumed. -/
theorem n06_chart_angle_seams
    {a b P : ℝ} {F : PolarPoint → PolarPoint}
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    {r : ℝ} (hr : r ∈ Ioo a b) :
    (F (r, 0)).2 = 0 ∧ (F (r, P)).2 = P := by
  have hzero : (F (r, 0)).2 = 0 := by
    have he := congrArg Prod.snd (hreflect (r, 0) ⟨hr, mem_univ _⟩)
    simp only [neg_zero] at he
    change (F (r, 0)).2 = -(F (r, 0)).2 at he
    linarith
  refine ⟨hzero, ?_⟩
  have he := congrArg Prod.snd (hperiod (r, 0) ⟨hr, mem_univ _⟩)
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.snd_add, hzero] using he

/-- Extend the already proved open-strip IVT result to the exact
half-open period used by the original measures. -/
theorem n06_chart_mapsTo_halfPeriod
    {a b c d P : ℝ} {F : PolarPoint → PolarPoint} (hP : 0 < P)
    (hF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hcont : ContinuousOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, P)) = F p + (0, P))
    (hreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2)) :
    MapsTo F (Ioo a b ×ˢ Ioc 0 P) (Ioo c d ×ˢ Ioc 0 P) := by
  have hopen := chart_mapsTo_openAngularStrip hP hF hinj hcont hperiod hreflect
  intro p hp
  by_cases htop : p.2 = P
  · have hpfull : p ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
    refine ⟨(hF hpfull).1, ?_⟩
    have he : p = (p.1, P) := Prod.ext rfl htop
    rw [he, (n06_chart_angle_seams hperiod hreflect hp.1).2]
    exact ⟨hP, le_rfl⟩
  · have hi := hopen (show p ∈ Ioo a b ×ˢ Ioo 0 P from
      ⟨hp.1, hp.2.1, lt_of_le_of_ne hp.2.2 htop⟩)
    exact ⟨hi.1, hi.2.1, hi.2.2.le⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Both genuine current maps preserve the measured half-period tiles.
The inverse equivariance is derived from the actual inverse identities. -/
theorem n06_canonicalChart_halfPeriod_maps
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    MapsTo (K.chart z m)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    MapsTo (K.inverseChart z m)
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hK := (n06_N04_qualitative_parts h04).1
  have hc := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hreflection := hK.2.2.2.2.2.2.2.2.2.1 z hz hs m
  have hinverseReflection := hK.2.2.2.2.2.2.2.2.2.2 z hz hs m
  have hpF : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hc.2.2.2.2.2.2.2 p hp).2.2.1
  have hpG : ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) :=
    fun _ hp => inverseChart_periodic_of_chart_periodic
      hc.2.1 hc.2.2.1 hc.2.2.2.1 hpF hp
  have hinjG : InjOn (K.inverseChart z m) (canonicalOpen S K m) := by
    intro p hp q hq heq
    exact (hc.2.2.2.1 p hp).symm.trans
      ((congrArg (K.chart z m) heq).trans (hc.2.2.2.1 q hq))
  exact ⟨n06_chart_mapsTo_halfPeriod Real.pi_pos hc.1
      (canonicalChart_injOn hK hz hs m) hc.2.2.2.2.1.continuousOn hpF
      (fun p hp => (hreflection p hp).1),
    n06_chart_mapsTo_halfPeriod Real.pi_pos hc.2.1 hinjG
      hc.2.2.2.2.2.1.continuousOn hpG hinverseReflection⟩

/-- The actual current chart is a bijection of the original measured
rectangles. Its angular coordinate is allowed to vary with both inputs. -/
theorem n06_canonicalChart_halfPeriod_bijOn
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    BijOn (K.chart z m)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  obtain ⟨hF, hG⟩ := n06_canonicalChart_halfPeriod_maps h04 hz hs m
  have hK := (n06_N04_qualitative_parts h04).1
  have hc := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      physicalPieceOpen S K m := fun _ hp => ⟨hp.1, mem_univ _⟩
  refine ⟨hF, ?_, ?_⟩
  · exact (canonicalChart_injOn hK hz hs m).mono hsub
  · intro p hp
    exact ⟨K.inverseChart z m p, hG hp, hc.2.2.2.1 p ⟨hp.1, mem_univ _⟩⟩

/-- Null-set transport through the actual current chart on precisely the
same half-period measures; no angular-identity premise is present. -/
theorem n06_canonicalChart_ae_iff
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (P : PolarPoint → Prop) :
    (∀ᵐ y ∂canonicalMeasure S K m, P y) ↔
      ∀ᵐ x ∂volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi),
        P (K.chart z m x) := by
  obtain ⟨hF, hG⟩ := n06_canonicalChart_halfPeriod_maps h04 hz hs m
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  exact n05_diffeomorphism_ae_iff
    (measurableSet_Ioo.prod measurableSet_Ioc) (measurableSet_Ioo.prod measurableSet_Ioc)
    hF hG (fun p hp => hc.2.2.1 p ⟨hp.1, mem_univ _⟩)
    (fun p hp => hc.2.2.2.1 p ⟨hp.1, mem_univ _⟩)
    ((hc.2.2.2.2.1.differentiableOn (by simp)).mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
    ((hc.2.2.2.2.2.1.differentiableOn (by simp)).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)) P

/-- Integrability under the genuine current change of coordinates. -/
theorem n06_canonicalChart_integrable_iff
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (g : PolarPoint → ℝ) :
    Integrable g (canonicalMeasure S K m) ↔
      Integrable (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p))
        (volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  have hb := n06_canonicalChart_halfPeriod_bijOn h04 hz hs m
  have he := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Ioo.prod measurableSet_Ioc)
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [IntegrableOn, canonicalMeasure, ← n05_planeJacobian_eq_det, smul_eq_mul] using he

/-- The same actual Jacobian gives the Bochner integral identity, with
no smoothness, periodicity, or support assumption on the integrand. -/
theorem n06_canonicalChart_integral
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (g : PolarPoint → ℝ) :
    (∫ p, g p ∂canonicalMeasure S K m) =
      ∫ p, |planeJacobian (K.chart z m) p| * g (K.chart z m p)
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hb := n06_canonicalChart_halfPeriod_bijOn h04 hz hs m
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_Ioo.prod measurableSet_Ioc)
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [canonicalMeasure, ← n05_planeJacobian_eq_det, smul_eq_mul] using he

/-- The nonnegative integral formula is valid before integrability has
been established and therefore also supports countable-piece estimates. -/
theorem n06_canonicalChart_lintegral
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (g : PolarPoint → ENNReal) :
    (∫⁻ p, g p ∂canonicalMeasure S K m) =
      ∫⁻ p, ENNReal.ofReal |planeJacobian (K.chart z m) p| * g (K.chart z m p)
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hb := n06_canonicalChart_halfPeriod_bijOn h04 hz hs m
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Ioo.prod measurableSet_Ioc)
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [canonicalMeasure, ← n05_planeJacobian_eq_det] using he

end ContinuousFlexibility.Statements
