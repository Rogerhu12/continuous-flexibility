import ContinuousFlexibility.Analysis.N06PrimitivePrincipalModeBound
import ContinuousFlexibility.Analysis.N06PrimitiveReferenceBudget
import ContinuousFlexibility.Analysis.N07aAngularReferenceInverse
import ContinuousFlexibility.Analysis.N07aVolumeWeightBounds

/-!
# The original weighted source budget for every principal block

The input is one genuine band of the same source level.  The original
reference inverse preserves that band, including its three scalar
components.  The actual RHS budget and the positive height gain absorb
the reference energy envelope only after all length factors are present.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements CanonicalGeometry
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

private theorem n06_angularWeight_sameOrder_transfer (b j l : ℕ) :
    Real.sqrt (n07aAngularJetWeightSq b l) ≤
      (2 * n07aAngularBlockWeightConstant b 0) *
        Real.sqrt (n07aAngularJetWeightSq b j) * n07aAngularGap j l ^ b := by
  have h := n07aAngularJetWeight_root_block_split b 0 j l
  simp only [Nat.add_zero] at h
  exact h.trans_eq (by ring)

private theorem n06_principal_weighted_multiply
    {v J L gap X e H ρ tail S e₀ W a C M : ℝ}
    (hv : 0 ≤ v) (hJ : 0 ≤ J) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (htail : 0 ≤ tail) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hweight : L ≤ C * J * gap)
    (hmode : gap * X ≤ e * H * ρ * tail * S)
    (hsource : J * S ≤ e₀ * W * a)
    (habsorb : v * H * W * (e * e₀) ≤ M) :
    v * L * X ≤ ρ * tail * ((C * M) * a) := by
  calc
    v * L * X ≤ v * (C * J * gap) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hv) hX
    _ = (C * v * J) * (gap * X) := by ring
    _ ≤ (C * v * J) * (e * H * ρ * tail * S) :=
      mul_le_mul_of_nonneg_left hmode (mul_nonneg (mul_nonneg hC hv) hJ)
    _ = (C * v * e * H * ρ * tail) * (J * S) := by ring
    _ ≤ (C * v * e * H * ρ * tail) * (e₀ * W * a) :=
      mul_le_mul_of_nonneg_left hsource
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hv) he) hH) hρ) htail)
    _ = (C * ρ * tail * a) * (v * H * W * (e * e₀)) := by ring
    _ ≤ (C * ρ * tail * a) * M :=
      mul_le_mul_of_nonneg_left habsorb
        (mul_nonneg (mul_nonneg (mul_nonneg hC hρ) htail) ha)
    _ = _ := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06WeightedBudgetLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06WeightedBudgetLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance n06WeightedBudgetUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n06WeightedBudgetUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n06WeightedBudgetGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06WeightedBudgetGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private def N06WeightedModeEstimates
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (d : ℕ) (e : ℕ → ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) m, K.positive m = true → ∀ j l : ℕ,
    n07aAngularBand m (hI m) j (n07aReferenceInverseField (B := B) F m) =
      n07aReferenceInverseField (B := B) F m →
    n07aAngularGap j l ^ b *
      ‖n07aAngularBand m (hI m) l
        (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
    e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      parameterGrading S (b + 4 + d) z * n07aAngularTail ((j : ℤ) - l) *
        (‖n07aReferenceInverseField (B := B) F m‖ +
          ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F)‖)

private def N06WeightedSourceEstimates
    (hV : IsVolumeModel T S K V) (href : ReferenceJets D T S C L K)
    (hI : ∀ m, K.left m < K.right m) (A₀ : ℝ) (e₀ : ℕ → ℝ) : Prop :=
  ∀ j (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
    ∃ a₀ : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a₀ m) ∧ ‖a₀‖ ≤ A₀ * ‖F‖ ∧
      ∀ m, Real.sqrt (n07aAngularJetWeightSq b j) *
        (‖n07aReferenceInverseField (B := B) F m‖ +
          ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤
        e₀ m * n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * a₀ m

private def N06WeightedInverseBands
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m) : Prop :=
  ∀ j (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1

private def N06WeightedPieceEstimate
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) (a : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  ∀ m l, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
    Real.sqrt (n07aAngularJetWeightSq b l) *
    ‖n07aAngularBand m (hI m) l
      (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
    parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * a m

private def N06WeightedPrincipalBudget
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
      N06WeightedPieceEstimate href hcur hI J N z hz j F a

set_option diagnostics true in
private theorem n06_weightedBudget_modes
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ d : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      N06WeightedModeEstimates href hcur hI J d e := by
  obtain ⟨d, hmodes⟩ := n06_primitivePrincipal_mode_bound
    hT hS h.1.1.1.1 h.1.1.2 h.1.2.2.2.2.1 h.2 href hcur hprincipal hI J
  exact (hmodes b).elim (fun e he => ⟨d, e, he.1, he.2.1, he.2.2⟩)

private theorem n06_weightedBudget_specialize
    {X Y : Type*} {I : Sort*} (PX : X → Prop) (PY QY : Y → Prop)
    (P : X → Y → I → Prop) (i : I)
    (h : ∃ x, PX x ∧ ∃ y, PY y ∧ QY y ∧ ∀ k : I, P x y k) :
    ∃ x, PX x ∧ ∃ y, PY y ∧ QY y ∧ P x y i :=
  h.elim (fun x hx => hx.2.elim (fun y hy =>
    ⟨x, hx.1, y, hy.1, hy.2.1, hy.2.2 i⟩))

set_option diagnostics true in
private theorem n06_weightedBudget_source
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hI : ∀ m, K.left m < K.right m) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ e₀ : ℕ → ℝ,
      N07aSampleSubpower T K e₀ ∧ (∀ m, 1 ≤ e₀ m) ∧
        N06WeightedSourceEstimates (B := B) h.2.2.1 href hI A₀ e₀ := by
  exact n06_weightedBudget_specialize
    (fun A : ℝ => 0 < A) (N07aSampleSubpower T K)
    (fun e : ℕ → ℝ => ∀ m, 1 ≤ e m)
    (fun A e hI => N06WeightedSourceEstimates (B := B) h.2.2.1 href hI A e) hI
    (n06_primitiveReference_energy_outer_budget
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href)

set_option diagnostics true in
private theorem n06_weightedBudget_inverse_bands
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) :
    N06WeightedInverseBands (B := B) h05.2.1 hI := by
  have hD : IsAccumulatingProfile D := h01.1.1
  have hrefz : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hrefs : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hmap (m : ℕ) : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m) := by
    simpa only [h04.1.referenceDomain m] using
      (h04.1.charts (C.referenceState, 0) hrefz hrefs m).2.1
  have hsm (m : ℕ) : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) := by
    simpa only [h04.1.referenceDomain m] using
      (h04.1.charts (C.referenceState, 0) hrefz hrefs m).2.2.2.2.1
  intro j F hF
  exact (n07a_referenceInverse_angularBand hD h01.1.2.2.2.1 h05 hI hR hAux hmap hsm F j).symm.trans
    (congrArg (fun G : V.level (3 / 4 : ℝ) 0 b => (B.inverse G).val.1) hF)

set_option diagnostics true in
private theorem n06_weightedBudget_piece
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (d : ℕ) (e e₀ : ℕ → ℝ) (he0 : ∀ m, 0 ≤ e m) (he₀one : ∀ m, 1 ≤ e₀ m)
    (hmode : N06WeightedModeEstimates href hcur hI J d e)
    (M : ℝ) (hM : 0 ≤ M)
    (habsorb : ∀ m, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * |e m * e₀ m| ≤ M)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b)
    (hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1)
    (a₀ : lp (fun _ : ℕ => ℝ) 2) (ha₀ : ∀ m, 0 ≤ a₀ m)
    (hpiece : ∀ m, Real.sqrt (n07aAngularJetWeightSq b j) *
      (‖n07aReferenceInverseField (B := B) F m‖ +
        ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤
      e₀ m * n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * a₀ m) :
    N06WeightedPieceEstimate href hcur hI J (b + 4 + d) z hz j F
      (((2 * n07aAngularBlockWeightConstant b 0) * M) • a₀) := by
  let C₀ : ℝ := 2 * n07aAngularBlockWeightConstant b 0
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by norm_num) (n07aAngularBlockWeightConstant_nonneg b 0)
  intro m l
  have ha : (((2 * n07aAngularBlockWeightConstant b 0) * M) • a₀) m =
      (C₀ * M) * a₀ m := by
    simp only [C₀, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hρ : 0 ≤ parameterGrading S (b + 4 + d) z := apply_nonneg _ _
  by_cases hm : K.positive m = true
  · have hband : n07aAngularBand m (hI m) j
        (n07aReferenceInverseField (B := B) F m) =
        n07aReferenceInverseField (B := B) F m :=
      congrArg (fun U : CanonicalUnknown S K => U.1 m) hU
    have hab := habsorb m
    rw [abs_of_nonneg (mul_nonneg (he0 m) (zero_le_one.trans (he₀one m)))] at hab
    rw [ha]
    exact n06_principal_weighted_multiply
      (inv_nonneg.mpr (n07aVolumeWeight_pos hD hT (3 / 4 : ℝ) 0 m).le)
      (Real.sqrt_nonneg _) (norm_nonneg _) (he0 m)
      (Real.rpow_pos_of_pos
        (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.1 _).le
      hρ (n07aAngularTail_nonneg _) (ha₀ m) hC₀
      (n06_angularWeight_sameOrder_transfer b j l)
      (hmode z hz F m hm j l hband) (hpiece m) hab
  · rw [n06PrimitivePrincipalSource_negative href hcur hI J z hz F m hm,
      map_zero, norm_zero, mul_zero, ha]
    exact mul_nonneg (mul_nonneg hρ (n07aAngularTail_nonneg _))
      (mul_nonneg (mul_nonneg hC₀ hM) (ha₀ m))

set_option diagnostics true in
private theorem n06_weightedBudget_assemble
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (hbands : N06WeightedInverseBands (B := B) hV hI)
    (d : ℕ) (e : ℕ → ℝ) (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (hmode : N06WeightedModeEstimates href hcur hI J d e)
    (A₀ : ℝ) (hA₀ : 0 < A₀) (e₀ : ℕ → ℝ)
    (he₀ : N07aSampleSubpower T K e₀) (he₀one : ∀ m, 1 ≤ e₀ m)
    (hsource : N06WeightedSourceEstimates (B := B) hV href hI A₀ e₀) :
    ∃ A : ℝ, 0 ≤ A ∧ N06WeightedPrincipalBudget hV href hcur hI J (b + 4 + d) A := by
  have heprod := N07aSampleSubpower.mul hD hT he he₀
  obtain ⟨M, hM, habsorb⟩ := heprod.volume_gain_absorption hD hT
    (by norm_num : (0 : ℝ) < 3 / 4) 0 (0 - B.lossMaterial)
  let C₀ : ℝ := 2 * n07aAngularBlockWeightConstant b 0
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by norm_num) (n07aAngularBlockWeightConstant_nonneg b 0)
  refine ⟨(C₀ * M) * A₀, mul_nonneg (mul_nonneg hC₀ hM.le) hA₀.le, ?_⟩
  intro z hz j F hF
  have hU := hbands j F hF
  obtain ⟨a₀, ha₀, hanorm, hpiece⟩ := hsource j F hF hU
  refine ⟨(C₀ * M) • a₀, ?_, ?_, ?_⟩
  · intro m
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using
      mul_nonneg (mul_nonneg hC₀ hM.le) (ha₀ m)
  · calc
      ‖(C₀ * M) • a₀‖ = (C₀ * M) * ‖a₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC₀ hM.le)]
      _ ≤ (C₀ * M) * (A₀ * ‖F‖) :=
        mul_le_mul_of_nonneg_left hanorm (mul_nonneg hC₀ hM.le)
      _ = _ := by ring
  · exact n06_weightedBudget_piece hD hT href hcur hI J d e e₀ he0 he₀one hmode
      M hM.le habsorb z hz j F hU a₀ ha₀ hpiece

private theorem n06_weightedBudget_bind_packages
    {X Y Z W : Type*} (PXY : X → Y → Prop) (PZ : Z → Prop)
    (PW QW : W → Prop) (PZW : Z → W → Prop) (Goal : Prop)
    (hxy : ∃ x y, PXY x y)
    (hzw : ∃ z, PZ z ∧ ∃ w, PW w ∧ QW w ∧ PZW z w)
    (hcombine : ∀ x y, PXY x y → ∀ z, PZ z →
      ∀ w, PW w → QW w → PZW z w → Goal) : Goal :=
  hxy.elim (fun x hx => hx.elim (fun y hxy =>
    hzw.elim (fun z hz => hz.2.elim (fun w hw =>
      hcombine x y hxy z hz.1 w hw.1 hw.2.1 hw.2.2))))

set_option diagnostics true in
private theorem n06_weightedBudget_uniform
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ N06WeightedPrincipalBudget h.2.2.1 href hcur hI J N A := by
  have hbands : N06WeightedInverseBands (B := B) h.2.2.1 hI :=
    n06_weightedBudget_inverse_bands h.1.1.1.1 h.1.2.2.2.2.1 h.2 hR hAux hI
  exact n06_weightedBudget_bind_packages
    (fun (d : ℕ) (e : ℕ → ℝ) => N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      N06WeightedModeEstimates href hcur hI J d e)
    (fun A : ℝ => 0 < A) (N07aSampleSubpower T K)
    (fun e : ℕ → ℝ => ∀ m, 1 ≤ e m)
    (fun A e => N06WeightedSourceEstimates (B := B) h.2.2.1 href hI A e)
    (∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ N06WeightedPrincipalBudget h.2.2.1 href hcur hI J N A)
    (n06_weightedBudget_modes
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href hcur hprincipal hI J)
    (n06_weightedBudget_source
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href hI)
    (fun d e he A₀ hA₀ e₀ he₀ he₀one hsource =>
      ⟨b + 4 + d, n06_weightedBudget_assemble h.1.1.1.1.1.1 hT h.2.2.1
        href hcur hI J hbands d e he.1 he.2.1 he.2.2 A₀ hA₀ e₀ he₀ he₀one hsource⟩)

set_option diagnostics true in
theorem n06_primitivePrincipal_weighted_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j
        (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h.2.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
        ∀ m l, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
          Real.sqrt (n07aAngularJetWeightSq b l) *
          ‖n07aAngularBand m (hI m) l
            (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
          parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * a m := by
  exact n06_weightedBudget_uniform hT hS h href hcur hprincipal hR hAux hI J

end ContinuousFlexibility.Analysis
