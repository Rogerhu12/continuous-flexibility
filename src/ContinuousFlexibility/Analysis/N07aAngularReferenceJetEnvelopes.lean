import ContinuousFlexibility.Analysis.N07aAngularPhysicalJetEnvelopes
import ContinuousFlexibility.Analysis.N07aAngularReferenceTransport
import ContinuousFlexibility.Analysis.N07aInverseChartBounds
import ContinuousFlexibility.Analysis.N07aSourceAtInverseChart
import ContinuousFlexibility.Analysis.N07aAngularJacobianEnvelope

/-!
# Actual reference transport retains a positive material height gain

For a fixed admissible parameter the displayed current-to-reference
transport has genuine physical derivatives of every order. Their sampled
coefficient envelope is subpower, while the original H^(3/4) factor is
retained. This uses the physical height inverse at its actual point.
-/

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

def n07aReferenceRemainderField {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  let q := K.inverseChart z m (K.chart (C.referenceState, 0) m p)
  K.height (C.referenceState, 0) m p * ((K.height z m q)⁻¹ * f q)

private theorem n07a_fixedJet_weight_reorder (e w d : ℝ) :
    e * w * d = (e * d) * w := by ring

theorem n07aReferencePieceHeight_eq_remainder
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (u : HeightPair S) (m : ℕ) :
    n07aReferencePieceHeight C K z (K.inverseChart z) u.2 (heightPairField S u) m =
      fun p => n07aReferenceRemainderField C K z ((S.height (3 / 4 : ℝ)).decode u.1) m p +
        u.2 * S.chiLeft p.1 := by
  funext p
  simp only [n07aReferencePieceHeight, n07aReferenceRemainderField, heightPairField,
    add_sub_cancel_right, div_eq_mul_inv]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07aReferenceRemainderField_contDiffOn
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07aReferenceRemainderField C K z f m)
      (referencePhysicalPieceOpen S K m) := by
  have he : n07aReferenceRemainderField C K z f m =
      n07aReferencePieceHeight C K z (K.inverseChart z) 0 f m := by
    funext p
    simp only [n07aReferenceRemainderField, n07aReferencePieceHeight,
      zero_mul, sub_zero, add_zero, div_eq_mul_inv]
    ring
  rw [he]
  exact n07aReferencePieceHeight_contDiffOn hS h01 h04 hz hs
    (fun _ _ _ => rfl) 0 hf m

theorem n07a_decodedPhysical_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K
      (physicalPieceOpen S K (liftSectorParameter S C z))
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun _ => (S.height (3 / 4 : ℝ)).decode u) := by
  intro n
  let bounds := n07a_source_jets_at_inverseChart
    (S := S) (C := C) (L := L) (K := K) (A := S.height (3 / 4 : ℝ))
    hD hT (hS.1 (3 / 4 : ℝ)) (by norm_num) (by norm_num) hrefState h04 hRatio n c
  let e : ℕ → ℝ := bounds.choose
  have he := bounds.choose_spec.1
  have he0 := bounds.choose_spec.2.1
  have heb := bounds.choose_spec.2.2
  let d : ℝ := (S.height (3 / 4 : ℝ)).grading (c + n + 3) u
  have hc : 0 ≤ d := apply_nonneg _ _
  refine ⟨fun m => e m * d,
    N07aSampleSubpower.mul hD hT he (N07aSampleSubpower.const hD hT d),
    fun m => mul_nonneg (he0 m) hc, ?_⟩
  intro m p hp
  have hgeom := h04.1.charts _
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hrefState.liftSectorParameter_sector z) m
  have h := heb z hz u m (K.chart (liftSectorParameter S C z) m p) (hgeom.1 hp)
  have heq :
      ‖iteratedFDeriv ℝ n ((S.height (3 / 4 : ℝ)).decode u)
        (K.inverseChart (liftSectorParameter S C z) m
          (K.chart (liftSectorParameter S C z) m p))‖ =
      ‖iteratedFDeriv ℝ n ((S.height (3 / 4 : ℝ)).decode u) p‖ :=
    congrArg (fun x : PolarPoint =>
      ‖iteratedFDeriv ℝ n ((S.height (3 / 4 : ℝ)).decode u) x‖) (hgeom.2.2.1 p hp)
  exact heq.symm.le.trans (h.trans_eq (n07a_fixedJet_weight_reorder (e m) _ d))

theorem n07a_currentInverseChart_positive_fixedEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) :
    ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m y, y ∈ canonicalOpen S K m →
          ‖iteratedFDeriv ℝ n (K.inverseChart (liftSectorParameter S C z) m) y‖ ≤ e m := by
  let bounds := n07a_inverseChart_positive_jets hD hT href hcur
    (fun m => (h04.1.referenceBounds m).2.1) (fun m => (h04.1.referenceBounds m).1)
  let d : ℕ := bounds.choose
  have hd := bounds.choose_spec
  intro n hn
  let e : ℕ → ℝ := (hd n hn).choose
  have he := (hd n hn).choose_spec.1
  have he0 := (hd n hn).choose_spec.2.1
  have heb := (hd n hn).choose_spec.2.2
  let a : ℝ := 1 + CanonicalGeometry.parameterGrading S ((n - 1) + d) z
  have ha : 0 ≤ a := add_nonneg zero_le_one (apply_nonneg _ _)
  exact ⟨fun m => e m * a,
    N07aSampleSubpower.mul hD hT he (N07aSampleSubpower.const hD hT a),
    fun m => mul_nonneg (he0 m) ha, fun m y hy => heb z hz m y hy⟩

theorem n07a_currentCanonicalHeightInverse_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K) (fun _ => 1)
      (fun m y => (K.height (liftSectorParameter S C z) m
        (K.inverseChart (liftSectorParameter S C z) m y))⁻¹) := by
  let z' : AnnularState S × ℝ := liftSectorParameter S C z
  let V : ℕ → Set PolarPoint := canonicalOpen S K
  let G : ℕ → PolarPoint → PolarPoint := K.inverseChart z'
  have hV : ∀ m, IsOpen (V m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hc (m : ℕ) := h04.1.charts z' hz' hs m
  have hG : ∀ m, ContDiffOn ℝ ∞ (G m) (V m) := fun m => (hc m).2.2.2.2.2.1
  have hJ (m : ℕ) (y : PolarPoint) (hy : y ∈ V m) :
      ContDiffAt ℝ ∞ (planeJacobian (G m)) y :=
    ContinuousFlexibility.contDiffAt_planeJacobian ((hG m).contDiffAt ((hV m).mem_nhds hy))
  have hJne (m : ℕ) (y : PolarPoint) (hy : y ∈ V m) : planeJacobian (G m) y ≠ 0 := by
    apply abs_ne_zero.mp
    rw [n07a_actual_inverseChart_jacobian_abs h04.1 hz' hs m hy]
    exact inv_ne_zero (abs_ne_zero.mpr
      ((hc m).2.2.2.2.2.2.2 _ ((hc m).2.1 hy)).2.1)
  have hJb := n07a_planeJacobian_fixedEnvelope_of_positiveJets hD hT hV hG
    (n07a_currentInverseChart_positive_fixedEnvelope hD hT h04 href hcur z hz)
  have hJabs := hJb.abs (fun m y hy => (hJ m y hy).continuousAt) hJne
  have hJsm (m : ℕ) : ContDiffOn ℝ ∞ (fun y => |planeJacobian (G m) y|) (V m) :=
    fun y hy => ((hJ m y hy).abs (hJne m y hy)).contDiffWithinAt
  have hinterval := fun m => (h04.1.referenceBounds m).2.1
  obtain ⟨d, hd⟩ := n07a_canonicalAtomFields_sampleJetBounds hD hT href hcur hinterval
  have hsrc := n07a_fixedJetEnvelope_of_sampleJetBounds hD hT (hd .sourceFactorInverse) hV
    (n07a_canonicalAtomField_smooth hcur hinterval .sourceFactorInverse) z hz
  have hsrcsm := n07a_canonicalAtomField_smooth hcur hinterval .sourceFactorInverse z hz
  have hprod : N07aAngularFixedJetEnvelope T K V (fun _ => 1)
      (fun m y => n07aCanonicalAtomField D T S C L K .sourceFactorInverse z m y *
        |planeJacobian (G m) y|) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hV
      hsrcsm hJsm hsrc hJabs (fun _ => zero_le_one) (fun _ => zero_le_one)
  apply hprod.congr hV
  intro m y hy
  exact n07a_canonicalHeightInverse_eq_sourceFactorInverse h04 z hz' hs m hy

theorem n07a_currentReference_remainder_fixedJetEnvelopes
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u)) ∧
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (n07aReferenceRemainderField C K (liftSectorParameter S C z)
        ((S.height (3 / 4 : ℝ)).decode u)) := by
  let z' : AnnularState S × ℝ := liftSectorParameter S C z
  let W : ℕ → Set PolarPoint := physicalPieceOpen S K z'
  let R : ℕ → Set PolarPoint := referencePhysicalPieceOpen S K
  let V : ℕ → Set PolarPoint := canonicalOpen S K
  let w : ℕ → ℝ := fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  let f : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode u
  let Ψ : ℕ → PolarPoint → PolarPoint := K.inverseChart z'
  let Φ : ℕ → PolarPoint → PolarPoint := K.chart (C.referenceState, 0)
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  have hphysical := fun m => (h04.1.referenceBounds m).1
  have hinterval := fun m => (h04.1.referenceBounds m).2.1
  have hW : ∀ m, IsOpen (W m) := fun m => (h04.1.domains z' hz' hs m).1
  have hR : ∀ m, IsOpen (R m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hV : ∀ m, IsOpen (V m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hw (m : ℕ) : 0 ≤ w m := by
    have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
    exact mul_nonneg (Real.rpow_nonneg (hT.2.1 _ hm).2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (hT.2.1 _ hm).2.2.2) c))
  have hc (m : ℕ) := h04.1.charts z' hz' hs m
  have hr (m : ℕ) := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  simp only [h04.1.referenceDomain] at hr
  have hfs (m : ℕ) : ContDiffOn ℝ ∞ f (W m) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u).1.mono (h04.1.domains z' hz' hs m).2.2.1
  have hΨb := n07a_currentInverseChart_positive_fixedEnvelope hD hT h04 href hcur z hz
  have hfcomp : N07aAngularFixedJetEnvelope T K V w (fun m => f ∘ Ψ m) :=
    (n07a_decodedPhysical_fixedJetEnvelope hD hT hS h01.2.2.1 h04 hRatio z hz u c).comp
      hD hT hw (fun m => (hc m).2.1)
      (fun m y hy => (hfs m).contDiffAt ((hW m).mem_nhds ((hc m).2.1 hy)))
      (fun m y hy => (hc m).2.2.2.2.2.1.contDiffAt ((hV m).mem_nhds hy)) hΨb
  have hfcsm (m : ℕ) : ContDiffOn ℝ ∞ (f ∘ Ψ m) (V m) :=
    (hfs m).comp (hc m).2.2.2.2.2.1 (hc m).2.1
  have hInvsm (m : ℕ) : ContDiffOn ℝ ∞
      (fun y => (K.height z' m (Ψ m y))⁻¹) (V m) :=
    ((hc m).2.2.2.2.2.2.1.comp (hc m).2.2.2.2.2.1 (hc m).2.1).inv
      (fun y hy => ((hc m).2.2.2.2.2.2.2 _ ((hc m).2.1 hy)).1.ne')
  have hprod : N07aAngularFixedJetEnvelope T K V w
      (fun m y => (K.height z' m (Ψ m y))⁻¹ * (f ∘ Ψ m) y) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hV hInvsm hfcsm
      (n07a_currentCanonicalHeightInverse_fixedJetEnvelope hD hT h01.2.2.1 h04 href hcur z hz)
      hfcomp (fun _ => zero_le_one) hw
  have hcan : N07aAngularFixedJetEnvelope T K V w
      (fun m => canonicalHeight S K z' m f) := by
    apply hprod.congr hV
    intro m y _
    simp only [canonicalHeight, Ψ, Function.comp_apply, div_eq_mul_inv, mul_comm]
  have hcans (m : ℕ) : ContDiffOn ℝ ∞ (canonicalHeight S K z' m f) (V m) :=
    (hfcsm m).div
      ((hc m).2.2.2.2.2.2.1.comp (hc m).2.2.2.2.2.1 (hc m).2.1)
      (fun y hy => ((hc m).2.2.2.2.2.2.2 _ ((hc m).2.1 hy)).1.ne')
  have hΦb := n07a_physicalChart_positive_fixedEnvelope hD hT href hinterval hphysical
    (fun m a => (href.1 m a).1)
    (n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical)
  have hback : N07aAngularFixedJetEnvelope T K R w
      (fun m => canonicalHeight S K z' m f ∘ Φ m) :=
    hcan.comp hD hT hw (fun m => (hr m).1)
      (fun m p hp => (hcans m).contDiffAt ((hV m).mem_nhds ((hr m).1 hp)))
      (fun m p hp => (hr m).2.2.2.2.1.contDiffAt ((hR m).mem_nhds hp)) hΦb
  have hheights (m : ℕ) : ContDiffOn ℝ ∞
      (n07aPhysicalJetField K (C.referenceState, 0) m 2) (R m) :=
    n07a_physicalJetField_smooth_of_atoms (fun m a => (href.1 m a).1)
      m (hphysical m) 2
  have hbacks (m : ℕ) : ContDiffOn ℝ ∞
      (canonicalHeight S K z' m f ∘ Φ m) (R m) :=
    (hcans m).comp (hr m).2.2.2.2.1 (hr m).1
  have hfinal : N07aAngularFixedJetEnvelope T K R w
      (fun m p => n07aPhysicalJetField K (C.referenceState, 0) m 2 p *
        (canonicalHeight S K z' m f ∘ Φ m) p) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hR hheights hbacks
      (n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical 2) hback
      (fun _ => zero_le_one) hw
  refine ⟨hcan, hfinal.congr hR ?_⟩
  intro m p _
  simp only [n07aReferenceRemainderField, n07aPhysicalJetField, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Function.comp_apply, canonicalHeight, div_eq_mul_inv]
  ring

theorem n07a_currentCanonicalHeight_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u)) :=
  (n07a_currentReference_remainder_fixedJetEnvelopes
    hD hT hS h01 h04 href hcur hRatio z hz u c).1

theorem n07a_referenceRemainder_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (n07aReferenceRemainderField C K (liftSectorParameter S C z)
        ((S.height (3 / 4 : ℝ)).decode u)) :=
  (n07a_currentReference_remainder_fixedJetEnvelopes
    hD hT hS h01 h04 href hcur hRatio z hz u c).2

end ContinuousFlexibility.Analysis
