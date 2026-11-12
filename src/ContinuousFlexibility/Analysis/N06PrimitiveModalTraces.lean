import ContinuousFlexibility.Analysis.N06PrimitiveReferenceTransport
import ContinuousFlexibility.Analysis.N06CutTransmissionJets

/-!
# The original graph's modal root and cut traces from primitive radiality

The actual physical weak graph has one C1 representative for every mode.
Reference radiality identifies its restrictions with all canonical modal
representatives. One-sided derivative uniqueness gives their true endpoint
jets. At moving cuts the original N04 law is applied to the physical C1
representative through its genuine closed inverse.

There is no material-label, coordinate-cost, matching, or PDE hypothesis
beyond the original graph and the primitive reference radial identities.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open CanonicalGeometry ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private instance : SFinite angleMeasure := by unfold angleMeasure; infer_instance
private instance : NeZero angleMeasure := ⟨by
  intro h
  have he := congrArg (fun μ : Measure ℝ => μ univ) h
  simp only [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero] at he
  exact (ENNReal.ofReal_pos.mpr Real.pi_pos).ne' he⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- A radial canonical AE identity pulls back through the actual chart. -/
theorem n06_primitiveReference_radial_ae_pullback
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (m : ℕ) {P : ℝ → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)), P y) :
    ∀ᵐ r ∂volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m)),
      P ((K.chart (C.referenceState, 0) m (r, 0)).1) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hp : ∀ᵐ p ∂canonicalMeasure S K m, P p.1 := by
    rw [n06_canonicalMeasure_eq_radial_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hP
  have hangle : ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) m,
      (K.chart (C.referenceState, 0) m p).2 = p.2 := by
    intro p hp
    have hp' : p ∈ referencePhysicalPieceOpen S K m := by
      simpa only [h04.1.referenceDomain m] using hp
    simpa only using congrArg Prod.snd (hradial.1 m p hp').1
  have hxActual := (n05_canonicalChart_ae_iff h04 href hs m hangle
    (fun p => P p.1)).mp hp
  have hx : ∀ᵐ p ∂volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi),
      P (K.chart (C.referenceState, 0) m p).1 := by
    simpa only [h04.1.referenceDomain m, referencePhysicalPieceOpen,
      prod_inter_prod, inter_univ, univ_inter] using hxActual
  have hprod : (volume : Measure PolarPoint).restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))).prod angleMeasure := by
    exact (Measure.prod_restrict _ _).symm
  rw [hprod] at hx
  filter_upwards [Measure.ae_ae_of_ae_prod hx, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  obtain ⟨θ, hθ⟩ := hr.exists
  have he := (hradial.1 m (r, θ) ⟨hrI, mem_univ _⟩).1
  simpa only [he] using hθ


/-- Actual canonical mode representatives pull back to the same physical mode. -/
theorem n06_primitiveReference_modal_representation
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    {η W : PolarPoint → ℝ} (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hperiod : Function.Periodic η (0, Real.pi)) (m n : ℕ) {v : ℝ → ℝ}
    (hrep : W =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m η)
    (hmode : n06HalfCosineCoefficient W n
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v) :
    evenFourierCoefficient η n =ᵐ[volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m))]
      (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcoef := (n06_canonical_halfCosineCoefficient_congr_ae hrep n).symm.trans hmode
  have hpull := n06_primitiveReference_radial_ae_pullback h hradial m hcoef
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D :=
    (h04.1.referenceBounds m).2.2
  have hi := ae_restrict_of_ae_restrict_of_subset hsub (n06_physical_halfMode_integrable_ae hη n)
  filter_upwards [hpull, hi, ae_restrict_mem measurableSet_Ioo] with r hr hir hrI
  have hper : Function.Periodic (fun θ => η (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
  have he := n06_primitiveReferenceHeight_mode h hradial η m n hrI hper hir
  have hH : 0 < K.height (C.referenceState, 0) m (r, 0) :=
    (n05_reference_boundary_regular h04.1 href hs m (p := (r, 0))
      ⟨hrI.1.le, hrI.2.le⟩).2.2.2
  have hv : evenFourierCoefficient η n r / K.height (C.referenceState, 0) m (r, 0) =
      v ((K.chart (C.referenceState, 0) m (r, 0)).1) := he.symm.trans hr
  exact (div_eq_iff hH.ne').mp hv |>.trans (mul_comm _ _)


/-- One physical C1 mode represents all canonical pieces of the same
original graph element. Only actual representation, rather than prescribed
endpoint traces, is used to identify each restriction. -/
theorem n06N05_primitive_mode_representative
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (u : B.Space) (n : ℕ) :
    ∃ w : ℝ → ℝ, ContDiffOn ℝ 1 w (radialCore D) ∧
      ∀ m : ℕ, ∀ v : ℝ → ℝ, ContDiff ℝ 1 v →
        (n06HalfCosineCoefficient (u.val.1.1 m) n
          =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v) →
        EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
          v ((K.chart (C.referenceState, 0) m (r, 0)).1))
            (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
  obtain ⟨η, f, hrep, hgraph, _⟩ := n06N05_exists_physical_modal_traces h u
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  obtain ⟨r₀, hr₀L, hr₀R⟩ := exists_between (h04.1.referenceBounds 0).1
  have hr₀ : r₀ ∈ radialCore D := (h04.1.referenceBounds 0).2.2 ⟨hr₀L, hr₀R⟩
  obtain ⟨w, hwAE, hw⟩ := n06_remainder_mode_C1_representative
    h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph
    (hS.2.2.1.1.of_le (by simp)) u.val.1.2.1 n hr₀
  let rem : PolarPoint → ℝ := n06ReferenceRemainder S.chiLeft η u.val.1.2.1
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph.1
  have hχ : MemLp (fun p : PolarPoint => u.val.1.2.1 * S.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (continuous_const.mul (hS.2.2.1.1.continuous.comp continuous_fst))
  have hrem : MemLp rem 2 (radialPhysicalMeasure D) := hη.sub hχ
  obtain ⟨a, ha⟩ := hgraph.1
  have hp : Function.Periodic rem (0, Real.pi) :=
    n06_referenceRemainder_periodic ha.2.2.1 _
  refine ⟨w, hw, ?_⟩
  intro m v hv hmode
  have hmodal := n06_primitiveReference_modal_representation h.1 hradial
    hrem hp m n (hrep.1 m) hmode
  have hsub := (h04.1.referenceBounds m).2.2
  have hwAE' : evenFourierCoefficient rem n
      =ᵐ[volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))] w :=
    ae_restrict_of_ae_restrict_of_subset hsub hwAE
  have hAE : w =ᵐ[volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))]
      (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1)) := hwAE'.symm.trans hmodal
  have hc : ContinuousOn (fun r => K.height (C.referenceState, 0) m (r, 0) *
      v ((K.chart (C.referenceState, 0) m (r, 0)).1))
        (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    intro r hr
    have hb := n05_reference_boundary_regular h04.1 href hs m (p := (r, 0))
      ⟨hr.1.le, hr.2.le⟩
    exact (n06_radial_mode_pullback_contDiffAt hb.1 hb.2.1 hv).continuousAt.continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo (hw.continuousOn.mono hsub) hc

/-- The true canonical modal value and signed normal traces agree at a
root, as consequences of the same physical C1 representative. -/
theorem n06N05_primitive_canonicalMode_root_traces
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K)
    (u : B.Space) (ml mr n : ℕ) (vl vr : ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hroot : K.physicalRight ml ∈ radialCore D)
    {yl yr σl σr : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) yr σr β H ρ κ Hr)
    (hH : H 0 ≠ 0) (hρ : ρ 0 ≠ 0)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr) :
    vl yl = vr yr ∧ σl * deriv vl yl = σr * deriv vr yr := by
  obtain ⟨w, hw, he⟩ := n06N05_primitive_mode_representative hS h hradial u n
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hdw : DifferentiableAt ℝ w (K.physicalRight ml) :=
    (hw.contDiffAt (isOpen_Ioo.mem_nhds hroot)).differentiableAt (by norm_num)
  have hpull (m : ℕ) (v : ℝ → ℝ) {y σ : ℝ}
      (J : N06RootFirstJets (K.chart (C.referenceState, 0) m)
        (K.height (C.referenceState, 0) m) (K.physicalRight ml) y σ β H ρ κ Hr)
      (hv : ContDiff ℝ 1 v) :
      DifferentiableAt ℝ (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1)) (K.physicalRight ml) := by
    have hline : DifferentiableAt ℝ (fun r : ℝ => (r, (0 : ℝ)))
        (K.physicalRight ml) := differentiableAt_id.prodMk (differentiableAt_const (0 : ℝ))
    have hchart : DifferentiableAt ℝ (fun r => K.chart (C.referenceState, 0) m (r, 0))
        (K.physicalRight ml) := (J.chart_differentiable 0).comp (K.physicalRight ml) hline
    have hheight : DifferentiableAt ℝ (fun r => K.height (C.referenceState, 0) m (r, 0))
        (K.physicalRight ml) := (J.height_differentiable 0).comp (K.physicalRight ml) hline
    exact hheight.fun_mul
      ((hv.differentiable (by norm_num) _).comp (K.physicalRight ml) hchart.fst)
  have hL := n06_cauchyData_eq_of_eqOn_Ioo_left (h04.1.referenceBounds ml).1
    (hpull ml vl Jl hvl) hdw (he ml vl hvl hmodeL).symm
  have hright : K.physicalRight ml < K.physicalRight mr :=
    hjoin.trans_lt (h04.1.referenceBounds mr).1
  have heR : EqOn (fun r => K.height (C.referenceState, 0) mr (r, 0) *
      vr ((K.chart (C.referenceState, 0) mr (r, 0)).1)) w
        (Ioo (K.physicalRight ml) (K.physicalRight mr)) := by
    rw [hjoin]
    exact (he mr vr hvr hmodeR).symm
  have hR := cauchyData_eq_of_eqOn_Ioo_right hright (hpull mr vr Jr hvr) hdw heR
  have hvalue : vl yl = vr yr := by
    apply mul_left_cancel₀ hH
    simpa only [Jl.height_value 0, Jr.height_value 0, Jl.chart_value 0,
      Jr.chart_value 0] using hL.1.trans hR.1.symm
  refine ⟨hvalue, ?_⟩
  have hder := hL.2.trans hR.2.symm
  rw [Jl.radialMode_deriv (hvl.differentiable (by norm_num) yl) 0,
    Jr.radialMode_deriv (hvr.differentiable (by norm_num) yr) 0, hvalue] at hder
  apply mul_left_cancel₀ (mul_ne_zero hH hρ)
  change (H 0 * ρ 0) * (σl * deriv vl yl) =
    (H 0 * ρ 0) * (σr * deriv vr yr)
  linear_combination hder

private theorem n06_primitive_scalarHeight_mode_eqOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (m : ℕ) (w v : ℝ → ℝ)
    (he : EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
      v ((K.chart (C.referenceState, 0) m (r, 0)).1))
        (Ioo (K.physicalLeft m) (K.physicalRight m))) :
    EqOn (fun y => canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1) (y, 0))
      v (Ioo (K.left m) (K.right m)) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hc := h04.1.charts (C.referenceState, 0) href hs m
  intro y hy
  let x : PolarPoint := K.inverseChart (C.referenceState, 0) m (y, 0)
  have hp : (y, (0 : ℝ)) ∈ canonicalOpen S K m := ⟨hy, mem_univ _⟩
  have hxActual : x ∈ physicalPieceOpen S K (C.referenceState, 0) m := hc.2.1 hp
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    simpa only [h04.1.referenceDomain m] using hxActual
  have hshape := hradial.1 m x hx
  have hright : K.chart (C.referenceState, 0) m x = (y, 0) := hc.2.2.2.1 _ hp
  have hyx : (K.chart (C.referenceState, 0) m (x.1, 0)).1 = y := by
    rw [hshape.1] at hright
    exact congrArg Prod.fst hright
  have hH : K.height (C.referenceState, 0) m x ≠ 0 :=
    (hc.2.2.2.2.2.2.2 x hxActual).1.ne'
  change w x.1 / K.height (C.referenceState, 0) m x = v y
  apply (div_eq_iff hH).mpr
  have hmodeValue : w x.1 = K.height (C.referenceState, 0) m (x.1, 0) *
      v ((K.chart (C.referenceState, 0) m (x.1, 0)).1) := he hx.1
  rw [hmodeValue, hshape.2, hyx]
  ring

/-- The genuine closed inverse and one-sided derivative uniqueness
identify the canonical upper endpoint jets of an actual C1 scalar mode. -/
private theorem n06_primitive_scalarHeight_upper_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (m : ℕ) {w v : ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (radialCore D)) (hv : ContDiff ℝ 1 v)
    (he : EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
      v ((K.chart (C.referenceState, 0) m (r, 0)).1))
        (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hx : (K.inverseChart (C.referenceState, 0) m (K.right m, 0)).1 ∈ radialCore D) :
    canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1) (K.right m, 0) =
        v (K.right m) ∧
      radialPartial (canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1))
        (K.right m, 0) = deriv v (K.right m) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hp : (K.right m, (0 : ℝ)) ∈ canonicalClosed S K m :=
    ⟨⟨(h04.1.referenceBounds m).2.1.le, le_rfl⟩, mem_univ _⟩
  have hG := (n04b_inverseChart_contDiffAt_closed h04.1 href hs m hp).differentiableAt
    (by simp)
  have hb := h04.1.boundary (C.referenceState, 0) href hs m
  have hH := hb.2.2.2.2.1 _ (hb.2.1 hp)
  have hwx : DifferentiableAt ℝ (fun p : PolarPoint => w p.1)
      (K.inverseChart (C.referenceState, 0) m (K.right m, 0)) :=
    ((hw.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt
      (by norm_num)).comp _ differentiableAt_fst
  have hd : DifferentiableAt ℝ
      (canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1)) (K.right m, 0) := by
    change DifferentiableAt ℝ (fun p =>
      w (K.inverseChart (C.referenceState, 0) m p).1 /
        K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p)) _
    have hnum : DifferentiableAt ℝ
        (fun p => w (K.inverseChart (C.referenceState, 0) m p).1) (K.right m, 0) :=
      hwx.comp _ hG
    have hden : DifferentiableAt ℝ
        (fun p => K.height (C.referenceState, 0) m
          (K.inverseChart (C.referenceState, 0) m p)) (K.right m, 0) :=
      (hH.2.1.differentiableAt (by simp)).comp _ hG
    simpa only [div_eq_mul_inv] using hnum.fun_mul (hden.fun_inv hH.2.2.2.ne')
  have hslice := hasDerivAt_radial_slice hd
  have htrace := n06_cauchyData_eq_of_eqOn_Ioo_left (h04.1.referenceBounds m).2.1
    hslice.differentiableAt (hv.differentiable (by norm_num) (K.right m))
    (n06_primitive_scalarHeight_mode_eqOn h01 h04 hradial m w v he)
  exact ⟨htrace.1, hslice.deriv.symm.trans htrace.2⟩

/-- The actual reference inverse and original smooth-test cut law give
the affine trace relation of every mode of the same N05 graph. -/
theorem n06N05_primitive_canonicalMode_cut_traces
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K)
    (u : B.Space) (n k : ℕ) (vl vr : ℝ → ℝ)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).1) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).1) (K.right (K.cutPair n).1))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).2) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr) :
    vl (K.cutRadius n) = vr (K.cutRadius n) ∧
      deriv vl (K.cutRadius n) + deriv vr (K.cutRadius n) =
        -(2 * K.cutRadius n)⁻¹ * vl (K.cutRadius n) := by
  obtain ⟨w, hw, he⟩ := n06N05_primitive_mode_representative hS h hradial u k
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcut := h04.2.1.1.2 (C.referenceState, 0) href hs n
  have hxcut := hcut.2.1 ⟨(0 : ℝ), rfl⟩
  have hC := h01.2.2.2.1
  have hxD : (canonicalCutPoint S K (C.referenceState, 0) n 0).1 ∈ radialCore D :=
    ⟨(hC.1 n).1.trans hxcut.1.1, hxcut.1.2.trans (hC.1 n).2.2⟩
  obtain ⟨_, _, _, _, _, _, _, _, hRl, hRr⟩ := h04.2.1.1.1 n
  have hxL : (K.inverseChart (C.referenceState, 0) (K.cutPair n).1
      (K.right (K.cutPair n).1, 0)).1 ∈ radialCore D := by
    rw [hRl]
    exact hxD
  have hxR : (K.inverseChart (C.referenceState, 0) (K.cutPair n).2
      (K.right (K.cutPair n).2, 0)).1 ∈ radialCore D := by
    rw [hRr, hcut.1 0]
    exact hxD
  have hleft := n06_primitive_scalarHeight_upper_jets h01 h04 hradial
    (K.cutPair n).1 hw hvl (he _ _ hvl hmodeL) hxL
  have hright := n06_primitive_scalarHeight_upper_jets h01 h04 hradial
    (K.cutPair n).2 hw hvr (he _ _ hvr hmodeR) hxR
  rw [hRl] at hleft
  rw [hRr] at hright
  have htrans := n06_reference_cut_scalar_of_contDiffOn_one h01 h04 hw n 0
  rw [hleft.1, hright.1, hleft.2, hright.2] at htrans
  refine ⟨htrans.1.symm, ?_⟩
  rw [htrans.2]
  simp only [div_eq_mul_inv]
  ring

end ContinuousFlexibility.Statements
