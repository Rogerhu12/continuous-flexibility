module

public import ContinuousFlexibility.Analysis.N07aAngularPhysicalJetEnvelopes
public import ContinuousFlexibility.Analysis.N07aInverseChartBounds
public import ContinuousFlexibility.Analysis.N07aReferenceReturn
public import ContinuousFlexibility.Analysis.N07aCanonicalSourceRegularity

/-!
# The actual reference source coordinates retain the sampled weight

The physical height and the actual absolute Jacobian inverse multiply
the source before composition with the genuine reference inverse chart.
Only positive-order inverse-chart jets enter the finite chain rule.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

private theorem n07a_source_eq_physicalJets
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) :
    canonicalSource S K z m f =
      (fun p => n07aPhysicalJetField K z m 5 p *
        (n07aPhysicalJetField K z m 2 p * f p)) ∘ K.inverseChart z m := by
  funext p
  simp only [canonicalSource, n07aPhysicalJetField, Function.comp_apply,
    show (5 : Fin 6) = (4 : Fin 5).succ from by decide,
    Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_four,
    Matrix.tail_cons, Matrix.head_cons, div_eq_mul_inv]
  ring

theorem n07a_lift_zero_parameter :
    liftSectorParameter S C (0 : CanonicalGeometry.Parameter S) = (C.referenceState, 0) := by
  simp only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero, add_zero]

theorem n07a_zero_parameter_mem
    (h01 : N01Properties D T S C base loss ε) :
    (0 : CanonicalGeometry.Parameter S) ∈ sectorNeighborhood S base ε ε := by
  have h0 : sectorGrading S base (0 : StateDirections S) = 0 :=
    (sectorGrading S base).map_zero'
  exact ⟨by simpa only [Prod.fst_zero] using h0.trans_lt h01.2.1,
    by simpa only [Prod.snd_zero, abs_zero] using h01.2.1⟩

theorem n07a_referenceInverseChart_positive_fixedEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ m y, y ∈ canonicalOpen S K m →
        ‖iteratedFDeriv ℝ n (K.inverseChart (C.referenceState, 0) m) y‖ ≤ e m := by
  let bounds := n07a_inverseChart_positive_jets hD hT href hcur
    (fun m => (h04.1.referenceBounds m).2.1) (fun m => (h04.1.referenceBounds m).1)
  let d : ℕ := bounds.choose
  have hd := bounds.choose_spec
  intro n hn
  let e : ℕ → ℝ := (hd n hn).choose
  have he := (hd n hn).choose_spec.1
  have he0 := (hd n hn).choose_spec.2.1
  have heb := (hd n hn).choose_spec.2.2
  refine ⟨e, he, he0, fun m y hy => ?_⟩
  have h := heb 0 (n07a_zero_parameter_mem h01) m y hy
  have h0 : CanonicalGeometry.parameterGrading S (n - 1 + d)
      (0 : CanonicalGeometry.Parameter S) = 0 :=
    (CanonicalGeometry.parameterGrading S (n - 1 + d)).map_zero'
  have heq := congrArg (fun q : AnnularState S × ℝ =>
    ‖iteratedFDeriv ℝ n (K.inverseChart q m) y‖) (n07a_lift_zero_parameter (S := S) (C := C))
  have hfactor : e m * (1 + CanonicalGeometry.parameterGrading S (n - 1 + d)
      (0 : CanonicalGeometry.Parameter S)) = e m :=
    (congrArg (fun a : ℝ => e m * (1 + a)) h0).trans (by rw [add_zero, mul_one])
  exact (heq.symm.le.trans h).trans_eq hfactor

theorem n07a_referenceSource_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {f : ℕ → PolarPoint → ℝ}
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (referencePhysicalPieceOpen S K m))
    (hf : N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) w f) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K) w
      (fun m => canonicalSource S K (C.referenceState, 0) m (f m)) := by
  let z : AnnularState S × ℝ := (C.referenceState, 0)
  let W := referencePhysicalPieceOpen S K
  let U := canonicalOpen S K
  have hW : ∀ m, IsOpen (W m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hU : ∀ m, IsOpen (U m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hphysical := fun m => (h04.1.referenceBounds m).1
  have hcs (i : Fin 6) (m : ℕ) : ContDiffOn ℝ ∞ (n07aPhysicalJetField K z m i) (W m) :=
    n07a_physicalJetField_smooth_of_atoms (fun m a => (href.1 m a).1) m (hphysical m) i
  have hcb := n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical
  have hhf : N07aAngularFixedJetEnvelope T K W w
      (fun m p => n07aPhysicalJetField K z m 2 p * f m p) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hW
      (hcs 2) hfs (hcb 2) hf (fun _ => zero_le_one) hw
  have hprod : N07aAngularFixedJetEnvelope T K W w
      (fun m p => n07aPhysicalJetField K z m 5 p *
        (n07aPhysicalJetField K z m 2 p * f m p)) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hW
      (hcs 5) (fun m => (hcs 2 m).mul (hfs m))
      (hcb 5) hhf (fun _ => zero_le_one) hw
  have hprods (m : ℕ) : ContDiffOn ℝ ∞
      (fun p => n07aPhysicalJetField K z m 5 p *
        (n07aPhysicalJetField K z m 2 p * f m p)) (W m) :=
    (hcs 5 m).mul ((hcs 2 m).mul (hfs m))
  have hgeom (m : ℕ) := h04.1.charts z
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  simp only [z, h04.1.referenceDomain] at hgeom
  have hcompose := hprod.comp hD hT hw (fun m => (hgeom m).2.1)
    (fun m y hy => (hprods m).contDiffAt ((hW m).mem_nhds ((hgeom m).2.1 hy)))
    (fun m y hy => (hgeom m).2.2.2.2.2.1.contDiffAt ((hU m).mem_nhds hy))
    (n07a_referenceInverseChart_positive_fixedEnvelope hD hT h01 h04 href hcur)
  apply hcompose.congr hU
  intro m y _
  exact congrFun (n07a_source_eq_physicalJets z m (f m)) y

theorem n07a_referenceSource_piece_contDiffOn
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    {f : ℕ → PolarPoint → ℝ}
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (referencePhysicalPieceOpen S K m)) (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalSource S K (C.referenceState, 0) m (f m))
      (canonicalOpen S K m) := by
  have hgeom := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  rw [h04.1.referenceDomain m] at hgeom
  have hcs (i : Fin 6) := n07a_physicalJetField_smooth_of_atoms
    (fun m a => (href.1 m a).1) m (h04.1.referenceBounds m).1 i
  have hsm := ((hcs 5).mul ((hcs 2).mul (hfs m))).comp
    hgeom.2.2.2.2.2.1 hgeom.2.1
  exact hsm.congr (fun y _ =>
    congrFun (n07a_source_eq_physicalJets (C.referenceState, 0) m (f m)) y)

end ContinuousFlexibility.Analysis
