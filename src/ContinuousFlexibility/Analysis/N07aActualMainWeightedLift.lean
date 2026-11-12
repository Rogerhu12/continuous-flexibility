import ContinuousFlexibility.Analysis.N07aActualMainWeightedBudget
import ContinuousFlexibility.Analysis.N07aAngularSequenceBandLift

/-!
# Actual one-high weighted realizations of the relative main blocks

The exact jet-weight ratio transfers the high input order to the same
reference inverse at its fixed base order. Both ordinary and commutator
blocks are realized in the prescribed volume graph, with unchanged
forgotten fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ENNReal ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aMainWeightedLiftLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aMainWeightedLiftLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aMainWeightedLiftUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aMainWeightedLiftUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aMainWeightedLiftGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aMainWeightedLiftGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private theorem n07a_mainLift_ratio_cancel
    (a b x y : ℝ) (hb : b ≠ 0) (h : a * x = b * y) : (a / b) * x = y := by
  apply mul_left_cancel₀ hb
  calc
    b * ((a / b) * x) = a * x := by field_simp
    _ = b * y := h

private theorem n07a_mainLift_split_rearrange (c τ ρ x y : ℝ) :
    c * ((τ * x) * ρ + τ * y) * 1 = c * τ * (ρ * x + y) := by
  ring

private theorem n07a_mainLift_majorant_norm
    (a₀ a₁ : lp (fun _ : ℕ => ℝ) 2) (c τ ρ : ℝ)
    (hc : 0 ≤ c) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) :
    ‖(c * τ) • (ρ • a₀ + a₁)‖ ≤ c * τ * (ρ * ‖a₀‖ + ‖a₁‖) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hτ)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hτ)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] using norm_add_le (ρ • a₀) a₁

private theorem n07a_mainLift_oneHigh_rearrange
    (c τ ρ A C g₀ g₁ x : ℝ) :
    c * τ * (ρ * (A * g₀ * x) + C * g₁ * x) =
      τ * ((c * A) * g₀ * (ρ * x) + (c * C) * g₁ * x) := by
  ring

theorem n07aAngularBand_truncate_norm_ratio
    (hV : IsVolumeModel T S K V) (γ w : ℝ) (hI : ∀ m, K.left m < K.right m)
    (b p j : ℕ) (U : V.level γ w (b + p)) :
    (Real.sqrt (n07aAngularJetWeightSq (b + p) j) /
        Real.sqrt (n07aAngularJetWeightSq b j)) *
      ‖n07aAngularLevelBand hV γ w hI b j
        (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)‖ =
      ‖n07aAngularLevelBand hV γ w hI (b + p) j U‖ := by
  have h := n07aAngularLevelLift_norm_ratio hV γ w hI b (b + p) j
    (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)
  rw [n07aAngularLevelLift_of_truncate] at h
  have hJ : 0 < Real.sqrt (n07aAngularJetWeightSq b j) :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le (n07aAngularJetWeightSq_one_le b j))
  have he : Real.sqrt (n07aAngularJetWeightSq (b + p) j) *
      ‖n07aAngularLevelBand hV γ w hI b j
        (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)‖ =
      Real.sqrt (n07aAngularJetWeightSq b j) *
        ‖n07aAngularLevelBand hV γ w hI (b + p) j U‖ := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (n07aAngularJetWeightSq_nonneg (b + p) j),
      Real.sq_sqrt (n07aAngularJetWeightSq_nonneg b j)]
    exact h.symm
  exact n07a_mainLift_ratio_cancel
    (Real.sqrt (n07aAngularJetWeightSq (b + p) j))
    (Real.sqrt (n07aAngularJetWeightSq b j))
    ‖n07aAngularLevelBand hV γ w hI b j
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)‖
    ‖n07aAngularLevelBand hV γ w hI (b + p) j U‖ hJ.ne' he

theorem n07a_actualRelativeMain_weighted_band_lift
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hI : ∀ m, K.left m < K.right m) :
    ∃ d : ℕ, ∀ t : ℝ, ∀ p : ℕ, ∃ A C₁ : ℝ, 0 ≤ A ∧ 0 ≤ C₁ ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∀ U : V.level (3 / 4 : ℝ) 0 (b + p), ∀ j l : ℕ, ∀ commute : Bool,
      let F := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
        (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
      ∃ W : V.level (3 / 4 : ℝ) t (b + p),
        V.forget (3 / 4 : ℝ) t (b + p) W = (fun m =>
          n07aAngularBand m (hI m) l
            ((if commute then ((l : ℝ) - j) else 1) •
              n07aRelativeMainSource (P := P) href hcur z hz F m (hI m))) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (A * parameterGrading S (b + d) z *
              ‖n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U‖ +
            C₁ * parameterGrading S (b + p + d) z * ‖F‖) := by
  let budget := n07a_actualRelativeMain_weighted_gap_budget hD hS hT h01 h02 h03 h04
    href hcur hprincipal h05 h06 hI
  let d : ℕ := budget.choose
  have hb := budget.choose_spec
  have hzref := n07a_reference_mem_stateNeighborhood h01
  have hsref := h01.2.2.1.stateSector
  have hmaps := h04.1.charts (C.referenceState, 0) hzref hsref
  have hmap (m : ℕ) : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m) := by
    simpa only [h04.1.referenceDomain] using (hmaps m).2.1
  have hsm (m : ℕ) : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) := by
    simpa only [h04.1.referenceDomain] using (hmaps m).2.2.2.2.1
  refine ⟨d, fun t p => ?_⟩
  let low := hb t b
  let A : ℝ := low.choose
  have hA : 0 < A := low.choose_spec.1
  have hlow := low.choose_spec.2
  let high := hb t (b + p)
  let C₁ : ℝ := high.choose
  have hC₁ : 0 < C₁ := high.choose_spec.1
  have hhigh := high.choose_spec.2
  let c : ℝ := n07aAngularBlockWeightConstant b p
  have hc : 0 ≤ c := n07aAngularBlockWeightConstant_nonneg b p
  refine ⟨c * A, c * C₁, mul_nonneg hc hA.le, mul_nonneg hc hC₁.le,
    fun z hz U j l commute => ?_⟩
  let F : V.level (3 / 4 : ℝ) 0 b := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
    (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
  have hF : n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F :=
    n07aAngularLevelBand_idempotent h05.2.1 (3 / 4 : ℝ) 0 hI b j _
  have hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 := by
    have h := n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j
    exact h.symm.trans (congrArg (fun G : V.level (3 / 4 : ℝ) 0 b =>
      (B.inverse G).val.1) hF)
  let lowMajorant := hlow z hz j F hF hU
  let a₀ : lp (fun _ : ℕ => ℝ) 2 := lowMajorant.choose
  have ha₀ : ∀ m, 0 ≤ a₀ m := lowMajorant.choose_spec.1
  have hn₀ : ‖a₀‖ ≤ A * parameterGrading S (b + d) z * ‖F‖ :=
    lowMajorant.choose_spec.2.1
  have hb₀ := lowMajorant.choose_spec.2.2
  let highMajorant := hhigh z hz j F hF hU
  let a₁ : lp (fun _ : ℕ => ℝ) 2 := highMajorant.choose
  have ha₁ : ∀ m, 0 ≤ a₁ m := highMajorant.choose_spec.1
  have hn₁ : ‖a₁‖ ≤ C₁ * parameterGrading S (b + p + d) z * ‖F‖ :=
    highMajorant.choose_spec.2.1
  have hb₁ := highMajorant.choose_spec.2.2
  let ρ : ℝ := Real.sqrt (n07aAngularJetWeightSq (b + p) j) /
    Real.sqrt (n07aAngularJetWeightSq b j)
  have hρ : 0 ≤ ρ := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let τ : ℝ := n07aAngularTail ((j : ℤ) - l)
  have hτ : 0 ≤ τ := by unfold τ n07aAngularTail; positivity
  let a : lp (fun _ : ℕ => ℝ) 2 := (c * τ) • (ρ • a₀ + a₁)
  have ha (m : ℕ) : a m = c * τ * (ρ * a₀ m + a₁ m) := by
    simp only [a, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ha0 (m : ℕ) : 0 ≤ a m := by
    rw [ha]
    exact mul_nonneg (mul_nonneg hc hτ) (add_nonneg (mul_nonneg hρ (ha₀ m)) (ha₁ m))
  let f : CanonicalSequence S K := fun m =>
    (if commute then ((l : ℝ) - j) else 1) •
      n07aRelativeMainSource (P := P) href hcur z hz F m (hI m)
  have hf (m : ℕ) : n07aAngularReflection m (f m) = f m := by
    let κ : ℝ := if commute then ((l : ℝ) - j) else 1
    let v : CanonicalL2 S K m := n07aRelativeMainSource (P := P) href hcur z hz F m (hI m)
    have hv : n07aAngularReflection m v = v :=
      n07aRelativeMainSource_reflection hS h01 h03 h04 href hcur h05.2.1 z hz F m (hI m)
    exact ((n07aAngularReflection m).map_smul κ v).trans
      (congrArg (fun w : CanonicalL2 S K m => κ • w) hv)
  have hpiece (m : ℕ) : (n07aVolumeWeight T K (3 / 4 : ℝ) t m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq (b + p) l) *
        ‖n07aAngularBand m (hI m) l (f m)‖ ≤ ‖a m‖ := by
    have hanorm : ‖a m‖ = c * τ * (ρ * a₀ m + a₁ m) :=
      (Real.norm_eq_abs (a m)).trans ((abs_of_nonneg (ha0 m)).trans (ha m))
    have hl := n07aAngularBlock_weighted_split b p j l
      (inv_pos.mpr (n07aVolumeWeight_pos hD hT _ _ m)).le (norm_nonneg
        (n07aAngularBand m (hI m) l (f m)))
      (A := τ * a₀ m) (C := τ * a₁ m) (a := 1)
      (by simpa only [mul_one] using hb₀ l commute m)
      (by simpa only [mul_one] using hb₁ l commute m)
    exact hl.trans_eq ((n07a_mainLift_split_rearrange c τ ρ (a₀ m) (a₁ m)).trans hanorm.symm)
  let W : V.level (3 / 4 : ℝ) t (b + p) :=
    n07aAngularSequenceBandLift hD hT h05.2.1 (3 / 4 : ℝ) t hI (b + p) l f hf a hpiece
  refine ⟨W, n07aAngularSequenceBandLift_forget hD hT h05.2.1 _ _ hI _ _ f hf a hpiece, ?_⟩
  have hn : ‖a‖ ≤ c * τ * (ρ * ‖a₀‖ + ‖a₁‖) :=
    n07a_mainLift_majorant_norm a₀ a₁ c τ ρ hc hτ hρ
  calc
    ‖W‖ ≤ ‖a‖ := n07aAngularSequenceBandLift_norm_le hD hT h05.2.1 _ _ hI _ _ f hf a hpiece
    _ ≤ c * τ * (ρ * ‖a₀‖ + ‖a₁‖) := hn
    _ ≤ c * τ * (ρ * (A * parameterGrading S (b + d) z * ‖F‖) +
        C₁ * parameterGrading S (b + p + d) z * ‖F‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hn₀ hρ) hn₁)
        (mul_nonneg hc hτ)
    _ = τ * ((c * A) * parameterGrading S (b + d) z * (ρ * ‖F‖) +
        (c * C₁) * parameterGrading S (b + p + d) z * ‖F‖) :=
      n07a_mainLift_oneHigh_rearrange c τ ρ A C₁
        (parameterGrading S (b + d) z) (parameterGrading S (b + p + d) z) ‖F‖
    _ = _ := congrArg (fun x : ℝ =>
      τ * ((c * A) * parameterGrading S (b + d) z * x +
        (c * C₁) * parameterGrading S (b + p + d) z * ‖F‖))
      (n07aAngularBand_truncate_norm_ratio h05.2.1 (3 / 4 : ℝ) 0 hI b p j U)

end ContinuousFlexibility.Analysis
