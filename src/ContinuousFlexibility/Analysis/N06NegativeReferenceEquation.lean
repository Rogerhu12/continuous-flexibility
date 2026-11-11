import ContinuousFlexibility.Analysis.N06NegativeFiniteGreen
import ContinuousFlexibility.Analysis.N06ReferenceWeakIdentity
import ContinuousFlexibility.Analysis.N06ReferenceRemainderEquation
import ContinuousFlexibility.Analysis.N06CanonicalWeakTransport
import ContinuousFlexibility.Analysis.N06CurrentChartChange

/-!
# The same N05 graph in the actual negative reference coordinates

The correction agrees with the radial reference operator away from the
reflection angles. Their countable exceptional set is null, and the actual
coordinate diffeomorphism transports this equality to canonical measure.
This replaces the positive-piece coefficient-germ argument and applies to
either type of piece without asserting periodicity of the correction.

For negative pieces the sign is positive. The resulting forcing retains
the original source, the actual left cutoff, the nu column and the psi
column. The principal part is literally `d_yy - y d_theta_theta`; its
potential is retained as a multiplication term, not assumed radial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The original N03 height-space identity identifies the actual
transformed reference operator almost everywhere on every piece. -/
theorem n06_reference_source_test_ae
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    canonicalSource S K (C.referenceState, 0) m
        (divergenceOperator (L.coefficients (C.referenceState, 0)) φ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceTestOperator D φ) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have hc := h04.2.2.2.2.2.2.2.1 (C.referenceState, 0) hz hs m
  have hangle : ∀ᵐ p : PolarPoint ∂volume,
      p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2)) := by
    change ∀ᵐ p ∂((volume : Measure ℝ).prod volume),
      p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))
    exact Measure.quasiMeasurePreserving_snd.ae n06_ae_nonreflection_angle
  apply (n06_canonicalChart_ae_iff h04 hz hs m _).mpr
  filter_upwards [ae_restrict_of_ae hangle,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hθ hp
  have hrad : p.1 ∈ radialCore D := (h04.2.2.2.1 m).2.2 hp.1
  have hlocal := n05_reference_correctionOperator_eq_local hT hS h.1
    isOpen_univ hφ.contDiffOn (mem_univ p) ⟨hrad, mem_univ _⟩ hθ
  have heq : divergenceOperator (L.coefficients (C.referenceState, 0)) φ p =
      n06ReferenceTestOperator D φ p := hlocal.symm.trans
    (n06_originalReference_testOperator hD h01.2.2.1 hφ
      (hD.choose_spec.1.1.trans hrad.1).ne')
  simp only [canonicalSource, hc.2.2.1 p ⟨hp.1, mem_univ _⟩, heq]

/-- Compact tests transport the genuine reference graph equation on
either cylinder type. The type sign is retained throughout. -/
theorem n06_referenceGraph_canonicalWeakPairing_all
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {γ M₀ M₁ μ : ℝ} {η g : PolarPoint → ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, μ) (g, 0))
    (aL : ℝ) (W : CanonicalL2 S K m)
    (hW : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m (n06ReferenceRemainder χ η aL))
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, W p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, ((if K.positive m then -1 else (1 : ℝ)) *
        canonicalSource S K (C.referenceState, 0) m
          (n06ReferenceRemainderForcing D χ g μ aL) p) * φ p
            ∂canonicalMeasure S K m := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have hA : N04PartA D S C K base ε := (n06_N04_qualitative_parts h04).1
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  let Φ : PolarPoint → ℝ := n06CanonicalTestPullback S K (C.referenceState, 0) m φ
  let w := n06ReferenceRemainder χ η aL
  let f := n06ReferenceRemainderForcing D χ g μ aL
  have hΦ : RadialTest D Φ := n06CanonicalTestPullback_radialTest hA hz hs hφ
  have hΦperiod : Function.Periodic Φ (0, Real.pi) :=
    n06CanonicalTestPullback_periodic hA hz hs hφ
  obtain ⟨hIL, hIR, heq⟩ := n06_referenceRemainder_equation hD hb hχ hgraph aL hΦ
  have hwperiod : Function.Periodic w (0, Real.pi) :=
    n06_referenceRemainder_periodic (χ := χ) hgraph.1.choose_spec.2.2.1 aL
  have hfperiod : Function.Periodic f (0, Real.pi) :=
    n06_referenceRemainderForcing_periodic hgeom.2.2.1.1 hχ hgraph.2.1.2.2.1 μ aL
  have hPperiod := n06_referenceTestOperator_periodic hgeom.2.2.1.1 hΦ.1 hΦperiod
  have hhalf : radialCore D ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans (by linarith only [Real.pi_pos])⟩
  have hILhalf : IntegrableOn (fun p => w p * n06ReferenceTestOperator D Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    (show IntegrableOn (fun p => w p * n06ReferenceTestOperator D Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume from hIL).mono_set hhalf
  have hIRhalf : IntegrableOn (fun p => f p * Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    (show IntegrableOn (fun p => f p * Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume from hIR).mono_set hhalf
  have hzero : ∀ p, p ∉ physicalPieceOpen S K m →
      w p * n06ReferenceTestOperator D Φ p = 0 := by
    obtain ⟨J, hJ, hJsub, hJzero⟩ := n06CanonicalTestPullback_radialSupport hA hz hs hφ
    intro p hp
    have hpJ : p.1 ∉ J := fun hpJ => hp ⟨hJsub hpJ, mem_univ _⟩
    have hz0 : n06ReferenceTestOperator D Φ p = 0 :=
      r11b_radialPDE_test_zero_outside hgeom hΦ.1 hJ.isClosed hJzero hpJ p.2
    rw [hz0, mul_zero]
  have hmean := n06_physicalMean_pairing_eq_canonical hA hgeom.2.1.le hz hs m w
    (n06ReferenceTestOperator D Φ) (hwperiod.mul hPperiod) hILhalf hzero
  have hsource := n06_reference_source_test_ae hT hS h hz hs m hΦ.1
  have hleft : (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      w (r, θ) * n06ReferenceTestOperator D Φ (r, θ))) =
      Real.pi⁻¹ * ((if K.positive m then -1 else (1 : ℝ)) *
        ∫ p, W p * canonicalOperator S K L (C.referenceState, 0) m φ p
          ∂canonicalMeasure S K m) := by
    refine hmean.trans ?_
    apply congrArg (fun t : ℝ => Real.pi⁻¹ * t)
    calc
      _ = ∫ p, (if K.positive m then -1 else (1 : ℝ)) *
          (W p * canonicalOperator S K L (C.referenceState, 0) m φ p)
            ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hW, hsource,
          ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hWp hsp hp
        rw [← hWp, ← hsp,
          n06CanonicalTestPullback_source_operator hA hz hs ⟨hp.1, mem_univ _⟩]
        ring
      _ = _ := integral_const_mul _ _
  have hright := n06_physicalMean_test_source hA hgeom.2.1.le hz hs f
    (hfperiod.mul hΦperiod) hIRhalf
  have he : (if K.positive m then -1 else (1 : ℝ)) *
      (∫ p, W p * canonicalOperator S K L (C.referenceState, 0) m φ p
        ∂canonicalMeasure S K m) =
      ∫ p, canonicalSource S K (C.referenceState, 0) m f p * φ p
        ∂canonicalMeasure S K m :=
    mul_left_cancel₀ (inv_ne_zero Real.pi_ne_zero) (hleft.symm.trans (heq.trans hright))
  have hsign : (∫ p, W p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      (if K.positive m then -1 else (1 : ℝ)) *
        ∫ p, canonicalSource S K (C.referenceState, 0) m f p * φ p
          ∂canonicalMeasure S K m := by
    cases hm : K.positive m <;>
      simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at he ⊢ <;>
      linarith only [he]
  refine hsign.trans ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- The negative-piece forcing has the original source with all three
literal scalar columns subtracted. -/
def n06NegativeReferenceForcing (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ) :
    PolarPoint → ℝ := fun p =>
  F m p - U.2.1 * canonicalSource S K (C.referenceState, 0) m
    (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p -
  U.2.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D) p -
  U.2.2.2 * canonicalSource S K (C.referenceState, 0) m
    ((S.height (3 / 4 : ℝ)).decode S.psi) p

theorem n06N05_negative_canonicalWeakPairing
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u.val.1.1 m p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, n06NegativeReferenceForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p ∂canonicalMeasure S K m := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have h05 : N05Properties D T S C K V b B := h.2
  obtain ⟨_, η, f, hrep, hgraph⟩ := (h05.2.2.2.2.2.2.1 u.val).mp u.property
  have he := n06_referenceGraph_canonicalWeakPairing_all hT hS h.1 hz hs m
    hS.2.2.1.1 hgraph u.val.1.2.1 (u.val.1.1 m) (hrep.1 m) hφ
  simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul] at he
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [hrep.2 m] with p hp
  simp only [n06NegativeReferenceForcing, hp, n06ReferenceRemainderForcing,
    canonicalSource, div_eq_mul_inv]
  ring

/-- The actual negative normal form, including the original potential.
Only the coefficient germs on the open canonical strip are used. -/
theorem n06_negative_canonicalOperator
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalOperator S K L z m φ p =
      n06NegativePrincipalTest φ p + K.potential z m p * φ p := by
  have hB : N04PartB S C L K base ε := (n06_N04_qualitative_parts h04).2
  have hcoeff := hB.2.2.2.1 z hz hs m hm
  have ha : (K.coefficients z m).a =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hcoeff q hq).1
  have hb : (K.coefficients z m).b =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hcoeff q hq).2.1
  have hc : (K.coefficients z m).c =ᶠ[𝓝 p] (fun q => -q.1) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hcoeff q hq).2.2
  have hd := n06_divergenceOperator_congr_germ
    (L := K.coefficients z m) (L' := ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩)
    φ (p := p) ha hb hc
  have he := hB.2.2.1 z hz hs m φ hφ p hp
  simpa only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, hd,
    n06_negativePrincipal_divergence hφ] using he

/-- The same original N05 graph satisfies the genuine negative weak
equation. Neither a scalar modal equation nor a physical PDE is added as
an input; the potential may still depend on the angular variable. -/
theorem n06N05_negative_principal_potential_pairing
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u.val.1.1 m p *
      (n06NegativePrincipalTest φ p + K.potential (C.referenceState, 0) m p * φ p)
        ∂canonicalMeasure S K m) =
      ∫ p, n06NegativeReferenceForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p ∂canonicalMeasure S K m := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  calc
    _ = ∫ p, u.val.1.1 m p * canonicalOperator S K L (C.referenceState, 0) m φ p
        ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      rw [n06_negative_canonicalOperator h04 hz hs m hm hφ.1 ⟨hp.1, mem_univ _⟩]
    _ = _ := n06N05_negative_canonicalWeakPairing hT hS h u m hm hφ

end ContinuousFlexibility.Analysis
