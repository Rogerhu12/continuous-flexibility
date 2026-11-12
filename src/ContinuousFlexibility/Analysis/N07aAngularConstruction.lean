import ContinuousFlexibility.Analysis.N07aActualRelativeWeightedBlocks
import ContinuousFlexibility.Analysis.N07aWeightedCommutatorOperators
import ContinuousFlexibility.Analysis.N07aUniformAngularInverse
import ContinuousFlexibility.Analysis.N07aAngularMaterialLift
import ContinuousFlexibility.Analysis.N07aParameterNeighborhood
import ContinuousFlexibility.Statements.N07aRegularity

/-!
# All weighted orders of the original N06 inverse

The concrete coefficient and energy estimates produce the original
relative operator's blocks. Their Schur realization supplies the actual
bounded commutator. One low-order neighborhood makes the inverse
constants uniform; subtraction supplies the material weight without
changing the inverse or its forgotten source.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ENNReal NNReal

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

local instance n07aAngularConstructionLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aAngularConstructionLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aAngularConstructionLevelInner (γ t : ℝ) (s : ℕ) :
    InnerProductSpace ℝ (V.level γ t s) := Submodule.innerProductSpace _

private theorem n07a_angular_schur_numeric (τ A C N X Y : ℝ) :
    τ * (A * X + (C * N) * Y) = (τ * A) * X + (τ * C) * N * Y := by
  ring

private theorem n07a_angular_absorb_low_numeric
    {τ A C low N X Y : ℝ} (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hlow : low ≤ 1) (hX : 0 ≤ X) :
    τ * (A * low * X + C * N * Y) ≤ τ * (A * X + (C * N) * Y) := by
  apply mul_le_mul_of_nonneg_left _ hτ
  apply add_le_add _ le_rfl
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hA) hX

theorem n07a_angular_construction
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
    (h06 : N06Properties D S C K L V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      N07aAngularProperties S C K V b B P base' ε' := by
  have hV := h05.2.1
  have hI (m : ℕ) : K.left m < K.right m := (h04.2.2.2.1 m).2.1
  have hraw := n07a_actualRelative_weighted_band_lift hD hborder hS hT
    h01 h02 h03 h04 href hcur hprincipal hR hAux h05 h06 hI
  let d : ℕ := hraw.choose
  let A : ℝ → ℕ → ℝ := fun t p => (hraw.choose_spec t p).choose
  let C₁ : ℝ → ℕ → ℝ := fun t p => (hraw.choose_spec t p).choose_spec.choose
  have hA (t : ℝ) (p : ℕ) : 0 ≤ A t p :=
    (hraw.choose_spec t p).choose_spec.choose_spec.1
  have hC (t : ℝ) (p : ℕ) : 0 ≤ C₁ t p :=
    (hraw.choose_spec t p).choose_spec.choose_spec.2.1
  have hblocks (t : ℝ) (p : ℕ) :=
    (hraw.choose_spec t p).choose_spec.choose_spec.2.2
  let τ : ℝ := ∑' k : ℤ, n07aAngularTail k
  have hτ : 0 ≤ τ := tsum_nonneg n07aAngularTail_nonneg
  let a : ℕ → ℝ≥0 := fun p => ⟨τ * A 0 p, mul_nonneg hτ (hA 0 p)⟩
  let c : ℕ → ℝ≥0 := fun p => ⟨τ * C₁ 0 p, mul_nonneg hτ (hC 0 p)⟩
  let neighborhood := n07a_lowParameter_neighborhood (S := S) (base := base) h06.1 (b + d)
  let base' : ℕ := neighborhood.choose
  have hbase : base ≤ base' := neighborhood.choose_spec.1
  let ε' : ℝ := neighborhood.choose_spec.2.choose
  have he' : 0 < ε' := neighborhood.choose_spec.2.choose_spec.1
  have he : ε' ≤ ε := neighborhood.choose_spec.2.choose_spec.2.1
  have hsubset := neighborhood.choose_spec.2.choose_spec.2.2.1
  have hsmall := neighborhood.choose_spec.2.choose_spec.2.2.2
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  refine ⟨base', hbase, ε', he', he, d, fun t p => ?_⟩
  let angular := n07a_uniformAngularInverse hV (3 / 4 : ℝ) hI b a c p
  let Cp : ℝ := angular.choose
  have hCp : 0 < Cp := angular.choose_spec.1
  have hinverse := angular.choose_spec.2
  let aMaterial : ℝ := τ * A t p
  let cMaterial : ℝ := τ * C₁ t p
  have hat : 0 ≤ aMaterial := mul_nonneg hτ (hA t p)
  have hct : 0 ≤ cMaterial := mul_nonneg hτ (hC t p)
  let Ctp : ℝ := 1 + aMaterial * Cp + 2 * cMaterial
  have hCtp : 0 < Ctp := by dsimp only [Ctp]; positivity
  refine ⟨Ctp, hCtp, fun z hz F₀ Fts hF => ?_⟩
  have hzold : z ∈ sectorNeighborhood S base ε ε := hsubset hz
  have hzstate : liftSectorParameter S C z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hzold le_rfl
  have hzsector : stateSector S (liftSectorParameter S C z).1 :=
    h01.2.2.1.liftSectorParameter_sector z
  have hlow : parameterGrading S (b + d) z ≤ 1 := hsmall z hz
  let N : ℕ → ℝ≥0 := fun q =>
    ⟨1 + parameterGrading S (b + q + d) z, by positivity⟩
  have hN (q : ℕ) : (N q : ℝ) = 1 + parameterGrading S (b + q + d) z := rfl
  have hNmono : Monotone N := by
    intro q r hqr
    exact add_le_add le_rfl (hmono (Nat.add_le_add_right (Nat.add_le_add_left hqr b) d) z)
  have hN₁ (q : ℕ) : 1 ≤ (N q : ℝ) := by
    rw [hN]
    exact le_add_of_nonneg_right (apply_nonneg _ _)
  have hN₀ : (N 0 : ℝ) ≤ 2 := by
    have hsum : 1 + parameterGrading S (b + d) z ≤ 2 :=
      (add_le_add (le_refl (1 : ℝ)) hlow).trans_eq (by norm_num)
    simpa only [hN, Nat.add_zero] using hsum
  have hconcrete (v : ℝ) (q : ℕ) (U : V.level (3 / 4 : ℝ) 0 (b + q))
      (j l : ℕ) (commute : Bool) :
      ∃ W : V.level (3 / 4 : ℝ) v (b + q),
        V.forget (3 / 4 : ℝ) v (b + q) W = V.forget (3 / 4 : ℝ) 0 b
          ((if commute then ((l : ℝ) - j) else 1) •
            n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b l
              (P.relative (liftSectorParameter S C z)
                (n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j
                  (n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b q) U)))) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (A v q * ‖n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI (b + q) j U‖ +
            (C₁ v q * (N q : ℝ)) *
              ‖n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j
                (n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b q) U)‖) := by
    let result := hblocks v q z hzold U j l commute
    let W : V.level (3 / 4 : ℝ) v (b + q) := result.choose
    refine ⟨W, result.choose_spec.1, result.choose_spec.2.trans ?_⟩
    exact n07a_angular_absorb_low_numeric (n07aAngularTail_nonneg _) (hA v q) hlow
      (norm_nonneg _)
  let operators := exists_n07aWeightedCommutatorOperators hD hT hV
    (3 / 4 : ℝ) hI b (P.relative (liftSectorParameter S C z)) A
    (fun v q => C₁ v q * (N q : ℝ)) hA
    (fun v q => mul_nonneg (hC v q) (N q).coe_nonneg) hconcrete
  let Q : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b := operators.choose
  have hcomm := operators.choose_spec.1
  have hops := operators.choose_spec.2
  have hlevels (q : ℕ) (commute : Bool) (U : V.level (3 / 4 : ℝ) 0 (b + q)) :
      ∃ W : V.level (3 / 4 : ℝ) 0 (b + q),
        V.forget (3 / 4 : ℝ) 0 (b + q) W = V.forget (3 / 4 : ℝ) 0 b
          ((if commute then Q else P.relative (liftSectorParameter S C z))
            (n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b q) U)) ∧
        ‖W‖ ≤ (a q : ℝ) * ‖U‖ + (c q : ℝ) * (N q : ℝ) *
          ‖n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b q) U‖ := by
    let result := hops 0 le_rfl q commute
    let W : V.level (3 / 4 : ℝ) 0 (b + q) →L[ℝ] V.level (3 / 4 : ℝ) 0 (b + q) :=
      result.choose
    have hW := result.choose_spec
    exact ⟨W U, (hW U).1, (hW U).2.trans_eq
      (n07a_angular_schur_numeric τ (A 0 q) (C₁ 0 q) (N q : ℝ) ‖U‖
        ‖n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b q) U‖)⟩
  let F0s : V.level (3 / 4 : ℝ) 0 (b + p) :=
    n07aAngularMaterialToZero hD hT hV (Nat.cast_nonneg t) Fts
  have hFbase : n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0
      (Nat.le_add_right b p) F0s = F₀ := by
    apply hV.2.2.1 (3 / 4 : ℝ) 0 b
    exact ((n07aAngularLevelTruncate_forget hV (3 / 4 : ℝ) 0
      (Nat.le_add_right b p) F0s).trans
      (n07aAngularMaterialToZero_forget hD hT hV (Nat.cast_nonneg t) Fts)).trans hF
  let inverseLift := hinverse (P.relative (liftSectorParameter S C z)) Q
    (P.inverse (liftSectorParameter S C z)) N hNmono hN₁ hN₀ hlevels hcomm
    (fun F => ((h06.2 _ hzstate hzsector).2.2.2.2.1 F).1)
    (fun F => ((h06.2 _ hzstate hzsector).2.2.2.2.1 F).2)
    (h06.2 _ hzstate hzsector).2.2.2.2.2 F0s
  let U : V.level (3 / 4 : ℝ) 0 (b + p) := inverseLift.choose
  have hU := inverseLift.choose_spec.1.trans
    (congrArg (P.inverse (liftSectorParameter S C z)) hFbase)
  have hn := inverseLift.choose_spec.2.trans_eq
    (congrArg (fun F : V.level (3 / 4 : ℝ) 0 b => Cp * (‖F0s‖ + (N p : ℝ) * ‖F‖)) hFbase)
  have hUforget : V.forget (3 / 4 : ℝ) 0 (b + p) U = V.forget (3 / 4 : ℝ) 0 b
      (P.inverse (liftSectorParameter S C z) F₀) := by
    exact (n07aAngularLevelTruncate_forget hV (3 / 4 : ℝ) 0
      (Nat.le_add_right b p) U).symm.trans
      (congrArg (V.forget (3 / 4 : ℝ) 0 b) hU)
  have hUnorm : ‖U‖ ≤ Cp * (‖Fts‖ + (N p : ℝ) * ‖F₀‖) :=
    hn.trans (mul_le_mul_of_nonneg_left
      (add_le_add (n07aAngularMaterialToZero_norm_le hD hT hV (Nat.cast_nonneg t) Fts) le_rfl) hCp.le)
  let materialLift := n07aAngularRelativeInverse_materialLift_bound h06
    hzstate hzsector F₀ Fts hF U hUforget hat hct (N p).coe_nonneg hUnorm
    (fun U₁ hU₁ => by
      let result := hops t (Nat.cast_nonneg t) p false
      let J : V.level (3 / 4 : ℝ) 0 (b + p) →L[ℝ] V.level (3 / 4 : ℝ) (t : ℝ) (b + p) :=
        result.choose
      have hJ := result.choose_spec
      have hu : n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0
          (Nat.le_add_right b p) U₁ = P.inverse (liftSectorParameter S C z) F₀ := by
        apply hV.2.2.1 (3 / 4 : ℝ) 0 b
        exact (n07aAngularLevelTruncate_forget hV (3 / 4 : ℝ) 0
          (Nat.le_add_right b p) U₁).trans hU₁
      refine ⟨J U₁, ?_, ?_⟩
      · have hforget : V.forget (3 / 4 : ℝ) (t : ℝ) (b + p) (J U₁) =
            V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z)
              (n07aAngularLevelTruncate hV (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U₁)) := by
          simpa only [Bool.false_eq_true, ite_false] using (hJ U₁).1
        exact hforget.trans (congrArg (fun F : V.level (3 / 4 : ℝ) 0 b =>
          V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F)) hu)
      · have h := (hJ U₁).2.trans_eq (congrArg (fun F : V.level (3 / 4 : ℝ) 0 b =>
          τ * (A t p * ‖U₁‖ + (C₁ t p * (N p : ℝ)) * ‖F‖)) hu)
        exact h.trans_eq (n07a_angular_schur_numeric τ (A t p) (C₁ t p) (N p : ℝ)
          ‖U₁‖ ‖P.inverse (liftSectorParameter S C z) F₀‖))
  let Uts : V.level (3 / 4 : ℝ) (t : ℝ) (b + p) := materialLift.choose
  have hUts := materialLift.choose_spec.1
  have hUtsnorm := materialLift.choose_spec.2
  refine ⟨Uts, hUts, hUtsnorm.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hCtp.le
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg F₀)
  rw [hN]
  exact add_le_add le_rfl (hmono (by omega : b + p + d ≤ b + t + p + d) z)

end ContinuousFlexibility.Analysis
