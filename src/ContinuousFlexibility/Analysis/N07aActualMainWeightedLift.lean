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
  apply (mul_left_cancel₀ hJ.ne')
  calc
    _ = Real.sqrt (n07aAngularJetWeightSq (b + p) j) *
      ‖n07aAngularLevelBand hV γ w hI b j
        (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)‖ := by field_simp
    _ = _ := he

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
      ∀ U : V.level (3 / 4 : ℝ) 0 (b + p), ∀ j l (commute : Bool),
      let F := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
        (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
      ∃ W : V.level (3 / 4 : ℝ) t (b + p),
        V.forget (3 / 4 : ℝ) t (b + p) W = fun m =>
          n07aAngularBand m (hI m) l
            ((if commute then ((l : ℝ) - j) else 1) •
              n07aRelativeMainSource (P := P) href hcur z hz F m (hI m)) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (A * parameterGrading S (b + d) z *
              ‖n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U‖ +
            C₁ * parameterGrading S (b + p + d) z * ‖F‖) := by
  obtain ⟨d, hb⟩ := n07a_actualRelativeMain_weighted_gap_budget hD hS hT h01 h02 h03 h04
    href hcur hprincipal h05 h06 hI
  have hzref := n07a_reference_mem_stateNeighborhood h01
  have hsref := h01.2.2.1.stateSector
  have hmaps := h04.2.2.2.2.2.2.2.1 (C.referenceState, 0) hzref hsref
  have hmap (m : ℕ) : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (physicalPieceOpen S K m) := (hmaps m).2.1
  have hsm (m : ℕ) : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (physicalPieceOpen S K m) := (hmaps m).2.2.2.2.1
  refine ⟨d, fun t p => ?_⟩
  obtain ⟨A, hA, hlow⟩ := hb t b
  obtain ⟨C₁, hC₁, hhigh⟩ := hb t (b + p)
  let c := n07aAngularBlockWeightConstant b p
  have hc : 0 ≤ c := n07aAngularBlockWeightConstant_nonneg b p
  refine ⟨c * A, c * C₁, mul_nonneg hc hA.le, mul_nonneg hc hC₁.le,
    fun z hz U j l commute => ?_⟩
  let F := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
    (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
  have hF : n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F :=
    n07aAngularLevelBand_idempotent h05.2.1 (3 / 4 : ℝ) 0 hI b j _
  have hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 := by
    have h := n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j
    rw [hF] at h
    exact h.symm
  obtain ⟨a₀, ha₀, hn₀, hb₀⟩ := hlow z hz j F hF hU
  obtain ⟨a₁, ha₁, hn₁, hb₁⟩ := hhigh z hz j F hF hU
  let ρ := Real.sqrt (n07aAngularJetWeightSq (b + p) j) /
    Real.sqrt (n07aAngularJetWeightSq b j)
  have hρ : 0 ≤ ρ := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let τ := n07aAngularTail ((j : ℤ) - l)
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
    dsimp only [f]
    rw [map_smul, n07aRelativeMainSource_reflection hS h01 h03 h04 href hcur h05.2.1]
  have hpiece (m : ℕ) : (n07aVolumeWeight T K (3 / 4 : ℝ) t m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq (b + p) l) *
        ‖n07aAngularBand m (hI m) l (f m)‖ ≤ ‖a m‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 m), ha]
    have hl := n07aAngularBlock_weighted_split b p j l
      (inv_pos.mpr (n07aVolumeWeight_pos hD hT _ _ m)).le (norm_nonneg
        (n07aAngularBand m (hI m) l (f m)))
      (A := τ * a₀ m) (C := τ * a₁ m) (a := 1)
      (by simpa only [mul_one] using hb₀ l commute m)
      (by simpa only [mul_one] using hb₁ l commute m)
    exact hl.trans_eq (by dsimp only [c, ρ]; ring)
  let W := n07aAngularSequenceBandLift hD hT h05.2.1 (3 / 4 : ℝ) t hI (b + p) l f hf a hpiece
  refine ⟨W, n07aAngularSequenceBandLift_forget hD hT h05.2.1 _ _ hI _ _ f hf a hpiece, ?_⟩
  have hn : ‖a‖ ≤ c * τ * (ρ * ‖a₀‖ + ‖a₁‖) := by
    rw [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hτ)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hτ)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] using norm_add_le (ρ • a₀) a₁
  calc
    ‖W‖ ≤ ‖a‖ := n07aAngularSequenceBandLift_norm_le hD hT h05.2.1 _ _ hI _ _ f hf a hpiece
    _ ≤ c * τ * (ρ * ‖a₀‖ + ‖a₁‖) := hn
    _ ≤ c * τ * (ρ * (A * parameterGrading S (b + d) z * ‖F‖) +
        C₁ * parameterGrading S (b + p + d) z * ‖F‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hn₀ hρ) hn₁)
        (mul_nonneg hc hτ)
    _ = τ * ((c * A) * parameterGrading S (b + d) z * (ρ * ‖F‖) +
        (c * C₁) * parameterGrading S (b + p + d) z * ‖F‖) := by ring
    _ = _ := by
      rw [show ρ * ‖F‖ = ‖n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U‖ from
        n07aAngularBand_truncate_norm_ratio h05.2.1 (3 / 4 : ℝ) 0 hI b p j U]

end ContinuousFlexibility.Analysis
