module

public import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge
public import ContinuousFlexibility.Analysis.N06ReferenceProjectionTransport

/-!
# Exact reference transport from the primitive radial identities

Only the actual radial chart and height identities are used here. No
material-label window, coordinate estimate, or auxiliary coordinate
witness is needed to transport modes and finite angular projections.
Both transformations retain their genuine inverse and Jacobian.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open CanonicalGeometry ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The reference forward Jacobian is its actual radial derivative. -/
theorem n06_primitiveReference_planeJacobian_radial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    planeJacobian (K.chart (C.referenceState, 0) m) p =
      deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 := by
  have h01 := h.1.1.1
  have hcActual := (h.2.2.2.2.1.1.charts (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m).2.2.2.2.1
  have hc : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) := by
    simpa only [h.2.2.2.2.1.1.referenceDomain m] using hcActual
  let ξ : ℝ → ℝ := fun r => (K.chart (C.referenceState, 0) m (r, 0)).1
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hp0 : (p.1, (0 : ℝ)) ∈ referencePhysicalPieceOpen S K m :=
    ⟨hp.1, mem_univ (0 : ℝ)⟩
  have hc0 : ContDiffAt ℝ ∞ (K.chart (C.referenceState, 0) m) (p.1, 0) :=
    hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp0)
  have hlineAt : ContDiffAt ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) p.1 :=
    hline.contDiffAt
  have hξ : DifferentiableAt ℝ ξ p.1 :=
    (hc0.comp p.1 hlineAt).fst.differentiableAt (by simp)
  have hFD : HasFDerivAt (fun q : PolarPoint => (ξ q.1, q.2))
      (((ContinuousLinearMap.toSpanSingleton ℝ (deriv ξ p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (hξ.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hnear : K.chart (C.referenceState, 0) m =ᶠ[𝓝 p]
      (fun q : PolarPoint => (ξ q.1, q.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hradial.1 m q hq).1
  rw [planeJacobian, (hFD.congr_of_eventuallyEq hnear).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, zero_mul, mul_one, mul_zero, sub_zero, ξ]


/-- The actual inverse fixes the radial coordinate along a canonical circle. -/
theorem n06_primitiveReference_inverse_circle
    (hradial : ReferenceRadial S C K) (m : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) (θ : ℝ) :
    K.inverseChart (C.referenceState, 0) m (p.1, θ) =
      ((K.inverseChart (C.referenceState, 0) m p).1, θ) := by
  have hzero := hradial.2 m p hp
  simpa only [hzero] using hradial.2 m (p.1, θ) ⟨hp.1, mem_univ _⟩

/-- The exact height factor is constant on each reference angular circle. -/
theorem n06_primitiveReferenceHeight_circle
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) (θ : ℝ) :
    let x := K.inverseChart (C.referenceState, 0) m p
    canonicalHeight S K (C.referenceState, 0) m f (p.1, θ) =
      (K.height (C.referenceState, 0) m (x.1, 0))⁻¹ * f (x.1, θ) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hx := (h04.1.charts (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m).2.1 hp
  rw [h04.1.referenceDomain m] at hx
  have hq : ((K.inverseChart (C.referenceState, 0) m p).1, θ) ∈
      referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  dsimp only [canonicalHeight]
  rw [n06_primitiveReference_inverse_circle hradial m hp θ,
    (hradial.1 m _ hq).2]
  exact div_eq_inv_mul _ _

/-- Physical finite projection commutes pointwise with the actual
reference height transform, without any smoothness assumption on f. -/
theorem n06_primitiveReferenceHeight_projection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (I : Finset ℕ) (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K (C.referenceState, 0) m (referenceBasisProjection I f) p =
      referenceBasisProjection I (canonicalHeight S K (C.referenceState, 0) m f) p := by
  have he := n06_primitiveReferenceHeight_circle h hradial f m hp
  have hproj := n06_primitiveReferenceHeight_circle h hradial
    (referenceBasisProjection I f) m hp p.2
  rw [show (p.1, p.2) = p from Prod.eta p] at hproj
  rw [hproj]
  simp only [referenceBasisProjection, angularBasisProjection]
  simp_rw [he, referenceAngularCoefficient_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)


/-- The exact source factor, including its true Jacobian, is radial. -/
theorem n06_primitiveReferenceSource_circle
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) (θ : ℝ) :
    let x := K.inverseChart (C.referenceState, 0) m p
    canonicalSource S K (C.referenceState, 0) m f (p.1, θ) =
      (K.height (C.referenceState, 0) m (x.1, 0) /
        |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) x.1|) *
          f (x.1, θ) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hx := (h04.1.charts (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m).2.1 hp
  rw [h04.1.referenceDomain m] at hx
  have hq : ((K.inverseChart (C.referenceState, 0) m p).1, θ) ∈
      referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  dsimp only [canonicalSource]
  rw [n06_primitiveReference_inverse_circle hradial m hp θ,
    (hradial.1 m _ hq).2, n06_primitiveReference_planeJacobian_radial h hradial m hq]
  ring

/-- Finite physical projection commutes with the actual source transform. -/
theorem n06_primitiveReferenceSource_projection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (I : Finset ℕ) (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K (C.referenceState, 0) m (referenceBasisProjection I f) p =
      referenceBasisProjection I (canonicalSource S K (C.referenceState, 0) m f) p := by
  have he := n06_primitiveReferenceSource_circle h hradial f m hp
  have hproj := n06_primitiveReferenceSource_circle h hradial
    (referenceBasisProjection I f) m hp p.2
  rw [show (p.1, p.2) = p from Prod.eta p] at hproj
  rw [hproj]
  simp only [referenceBasisProjection, angularBasisProjection]
  simp_rw [he, referenceAngularCoefficient_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

/-- The normalized canonical and physical Fourier modes have exactly the
same reference height factor. -/
theorem n06_primitiveReferenceHeight_mode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (η : PolarPoint → ℝ) (m n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
    (hp : Function.Periodic (fun θ => η (r, θ)) Real.pi)
    (hi : IntervalIntegrable (fun θ => η (r, θ) * referenceAngularBasis n θ)
      volume 0 Real.pi) :
    n06HalfCosineCoefficient (canonicalHeight S K (C.referenceState, 0) m η) n
        ((K.chart (C.referenceState, 0) m (r, 0)).1) =
      evenFourierCoefficient η n r / K.height (C.referenceState, 0) m (r, 0) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcharts := h04.1.charts (C.referenceState, 0) href hs m
  rw [h04.1.referenceDomain m] at hcharts
  have hleft := hcharts.2.2.1
  let y := (K.chart (C.referenceState, 0) m (r, 0)).1
  let H := K.height (C.referenceState, 0) m (r, 0)
  have hinverse (θ : ℝ) : K.inverseChart (C.referenceState, 0) m (y, θ) = (r, θ) := by
    have hq : (r, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hr, mem_univ θ⟩
    have hchart := (hradial.1 m (r, θ) hq).1
    simpa only [hchart] using hleft (r, θ) hq
  have hheight (θ : ℝ) : canonicalHeight S K (C.referenceState, 0) m η (y, θ) =
      H⁻¹ * η (r, θ) := by
    have hq : (r, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hr, mem_univ θ⟩
    simp only [canonicalHeight, hinverse θ, (hradial.1 m (r, θ) hq).2]
    exact div_eq_inv_mul _ _
  change n06HalfCosineCoefficient (canonicalHeight S K (C.referenceState, 0) m η) n y =
    evenFourierCoefficient η n r / H
  calc
    _ = H⁻¹ * n06HalfCosineCoefficient η n r := by
      unfold n06HalfCosineCoefficient n06AngularCoefficient
      simp_rw [hheight, mul_assoc]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [n06_halfCosineCoefficient_eq_evenFourierCoefficient η n r hp hi]
      exact (div_eq_inv_mul _ _).symm


end ContinuousFlexibility.Statements
