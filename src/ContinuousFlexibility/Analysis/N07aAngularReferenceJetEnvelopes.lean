import ContinuousFlexibility.Analysis.N07aAngularPhysicalJetEnvelopes
import ContinuousFlexibility.Analysis.N07aAngularReferenceTransport
import ContinuousFlexibility.Analysis.N07aInverseChartBounds
import ContinuousFlexibility.Analysis.N07aSourceAtInverseChart

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

private theorem n07a_canonicalHeight_eq_physicalJets
    {S : PhysicalSpacesData} (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (f : PolarPoint → ℝ) :
    canonicalHeight S K z m f =
      (fun p => n07aPhysicalJetField K z m 3 p * f p) ∘ K.inverseChart z m := by
  funext p
  simp only [canonicalHeight, Function.comp_apply, n07aPhysicalJetField,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, div_eq_mul_inv]
  exact mul_comm _ _

private theorem n07a_referenceRemainder_eq_physicalJets
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (f : PolarPoint → ℝ) (m : ℕ) :
    n07aReferenceRemainderField C K z f m = fun p =>
      n07aPhysicalJetField K (C.referenceState, 0) m 2 p *
        (((fun q => n07aPhysicalJetField K z m 3 q * f q) ∘ K.inverseChart z m) ∘
          K.chart (C.referenceState, 0) m) p := by
  funext p
  simp only [n07aReferenceRemainderField, Function.comp_apply, n07aPhysicalJetField,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

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
      (physicalPieceOpen S K m) := by
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
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun _ => (S.height (3 / 4 : ℝ)).decode u) := by
  intro n
  let bounds := n07a_source_jets_at_inverseChart
    (S := S) (C := C) (L := L) (K := K) (A := S.height (3 / 4 : ℝ))
    hD hT (hS.1 (3 / 4 : ℝ)) (by norm_num) (by norm_num) hrefState h04 href n c
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
  have hgeom := h04.2.2.2.2.2.2.2.1 _
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

theorem n07a_currentReference_remainder_fixedJetEnvelopes
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u)) ∧
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (n07aReferenceRemainderField C K (liftSectorParameter S C z)
        ((S.height (3 / 4 : ℝ)).decode u)) := by
  let z' : AnnularState S × ℝ := liftSectorParameter S C z
  let W : ℕ → Set PolarPoint := physicalPieceOpen S K
  let V : ℕ → Set PolarPoint := canonicalOpen S K
  let w : ℕ → ℝ := fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  let f : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode u
  let g : ℕ → PolarPoint → ℝ := fun m p => n07aPhysicalJetField K z' m 3 p * f p
  let Ψ : ℕ → PolarPoint → PolarPoint := fun m => K.inverseChart z' m
  let Φ : ℕ → PolarPoint → PolarPoint := fun m => K.chart (C.referenceState, 0) m
  have hphysical := fun m => (h04.2.2.2.1 m).1
  have hinterval := fun m => (h04.2.2.2.1 m).2.1
  have hW : ∀ m, IsOpen (W m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hV : ∀ m, IsOpen (V m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hw (m : ℕ) : 0 ≤ w m := by
    have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
    exact mul_nonneg (Real.rpow_nonneg (hT.2.1 _ hm).2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (hT.2.1 _ hm).2.2.2) c))
  have hc (m : ℕ) := h04.2.2.2.2.2.2.2.1 z'
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) m
  have hr (m : ℕ) := h04.2.2.2.2.2.2.2.1 (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  have hfs (m : ℕ) : ContDiffOn ℝ ∞ f (W m) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u).1.mono
      (fun _ hp => ⟨(h04.2.2.2.1 m).2.2 hp.1, mem_univ _⟩)
  have hinvs (m : ℕ) : ContDiffOn ℝ ∞ (n07aPhysicalJetField K z' m 3) (W m) :=
    n07a_physicalJetField_smooth_of_atoms (fun m a => (hcur.1 z hz m a).1)
      m (hphysical m) 3
  have hgs (m : ℕ) : ContDiffOn ℝ ∞ (g m) (W m) := (hinvs m).mul (hfs m)
  have hgb : N07aAngularFixedJetEnvelope T K W w g := by
    have hmul := N07aAngularFixedJetEnvelope.mul hD hT hW hinvs hfs
      (n07a_currentPhysicalJetFields_fixedEnvelope hD hT href hcur hphysical z hz 3)
      (n07a_decodedPhysical_fixedJetEnvelope hD hT hS h01.2.2.1 h04 href z hz u c)
      (fun _ => zero_le_one) hw
    simpa only [one_mul] using hmul
  have hΨb : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m y, y ∈ V m → ‖iteratedFDeriv ℝ n (Ψ m) y‖ ≤ e m := by
    let bounds := n07a_inverseChart_positive_jets hD hT href hcur hinterval hphysical
    let d : ℕ := bounds.choose
    have hd := bounds.choose_spec
    intro n hn
    let e : ℕ → ℝ := (hd n hn).choose
    have he := (hd n hn).choose_spec.1
    have he0 := (hd n hn).choose_spec.2.1
    have heb := (hd n hn).choose_spec.2.2
    let c : ℝ := 1 + CanonicalGeometry.parameterGrading S ((n - 1) + d) z
    have hc0 : 0 ≤ c := add_nonneg zero_le_one (apply_nonneg _ _)
    exact ⟨fun m => e m * c,
      N07aSampleSubpower.mul hD hT he (N07aSampleSubpower.const hD hT c),
      fun m => mul_nonneg (he0 m) hc0, fun m y hy => heb z hz m y hy⟩
  have hcan : N07aAngularFixedJetEnvelope T K V w (fun m => g m ∘ Ψ m) :=
    hgb.comp hD hT hw (fun m => (hc m).2.1)
      (fun m y hy => (hgs m).contDiffAt ((hW m).mem_nhds ((hc m).2.1 hy)))
      (fun m y hy => (hc m).2.2.2.2.2.1.contDiffAt ((hV m).mem_nhds hy)) hΨb
  have hΦb := n07a_physicalChart_positive_fixedEnvelope hD hT href hinterval hphysical
    (fun m a => (href.1 m a).1)
    (n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical)
  have hcans (m : ℕ) : ContDiffOn ℝ ∞ (g m ∘ Ψ m) (V m) :=
    (hgs m).comp (hc m).2.2.2.2.2.1 (hc m).2.1
  have hback : N07aAngularFixedJetEnvelope T K W w (fun m => (g m ∘ Ψ m) ∘ Φ m) :=
    hcan.comp hD hT hw (fun m => (hr m).1)
      (fun m p hp => (hcans m).contDiffAt ((hV m).mem_nhds ((hr m).1 hp)))
      (fun m p hp => (hr m).2.2.2.2.1.contDiffAt ((hW m).mem_nhds hp)) hΦb
  have hheights (m : ℕ) : ContDiffOn ℝ ∞
      (n07aPhysicalJetField K (C.referenceState, 0) m 2) (W m) :=
    n07a_physicalJetField_smooth_of_atoms (fun m a => (href.1 m a).1)
      m (hphysical m) 2
  have hbacks (m : ℕ) : ContDiffOn ℝ ∞ ((g m ∘ Ψ m) ∘ Φ m) (W m) :=
    (hcans m).comp (hr m).2.2.2.2.1 (hr m).1
  have hfinal := N07aAngularFixedJetEnvelope.mul hD hT hW hheights hbacks
    (n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical 2) hback
    (fun _ => zero_le_one) hw
  constructor
  · apply hcan.congr hV
    intro m y _
    exact congrFun (n07a_canonicalHeight_eq_physicalJets K z' m f) y
  · have hfinal' : N07aAngularFixedJetEnvelope T K W w
        (fun m p => n07aPhysicalJetField K (C.referenceState, 0) m 2 p *
          ((g m ∘ Ψ m) ∘ Φ m) p) := by
      simpa only [one_mul] using hfinal
    apply hfinal'.congr hW
    intro m p _
    exact congrFun (n07a_referenceRemainder_eq_physicalJets C K z' f m) p

theorem n07a_currentCanonicalHeight_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u)) :=
  (n07a_currentReference_remainder_fixedJetEnvelopes
    hD hT hS h01 h04 href hcur z hz u c).1

theorem n07a_referenceRemainder_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (c : ℕ) :
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (n07aReferenceRemainderField C K (liftSectorParameter S C z)
        ((S.height (3 / 4 : ℝ)).decode u)) :=
  (n07a_currentReference_remainder_fixedJetEnvelopes
    hD hT hS h01 h04 href hcur z hz u c).2

end ContinuousFlexibility.Analysis
