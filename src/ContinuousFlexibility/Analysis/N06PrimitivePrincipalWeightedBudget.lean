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

set_option backward.isDefEq.respectTransparency false

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
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have h05 : N05Properties D T S C K V b B := h.2
  have hD : IsAccumulatingProfile D := h01.1.1
  obtain ⟨d, hmodes⟩ := n06_primitivePrincipal_mode_bound
    hT hS h01 h03 h04 h05 href hcur hprincipal hI J
  obtain ⟨e, he, he0, hmode⟩ := hmodes b
  obtain ⟨A₀, hA₀, e₀, he₀, he₀one, hsource⟩ :=
    n06_primitiveReference_energy_outer_budget hT hS h href
  have heprod := N07aSampleSubpower.mul hD hT he he₀
  obtain ⟨M, hM, habsorb⟩ := heprod.volume_gain_absorption hD hT
    (by norm_num : (0 : ℝ) < 3 / 4) 0 (0 - B.lossMaterial)
  let C₀ : ℝ := 2 * n07aAngularBlockWeightConstant b 0
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by norm_num) (n07aAngularBlockWeightConstant_nonneg b 0)
  refine ⟨b + 4 + d, (C₀ * M) * A₀,
    mul_nonneg (mul_nonneg hC₀ hM.le) hA₀.le, ?_⟩
  intro z hz j F hF
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
  have hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 :=
    (n07a_referenceInverse_angularBand hD h01.1.2.2.2.1 h05 hI hR hAux hmap hsm F j).symm.trans
      (congrArg (fun G : V.level (3 / 4 : ℝ) 0 b => (B.inverse G).val.1) hF)
  obtain ⟨a₀, ha₀, hanorm, hpiece⟩ := hsource hI j F hF hU
  let a : lp (fun _ : ℕ => ℝ) 2 := (C₀ * M) • a₀
  have ha (m : ℕ) : a m = (C₀ * M) * a₀ m := by
    simp only [a, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  refine ⟨a, (fun m => by rw [ha]; exact mul_nonneg (mul_nonneg hC₀ hM.le) (ha₀ m)),
    ?_, ?_⟩
  · calc
      ‖a‖ = (C₀ * M) * ‖a₀‖ := by
        rw [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC₀ hM.le)]
      _ ≤ (C₀ * M) * (A₀ * ‖F‖) :=
        mul_le_mul_of_nonneg_left hanorm (mul_nonneg hC₀ hM.le)
      _ = _ := by ring
  · intro m l
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
        (mul_nonneg (mul_nonneg hC₀ hM.le) (ha₀ m))

end ContinuousFlexibility.Analysis
