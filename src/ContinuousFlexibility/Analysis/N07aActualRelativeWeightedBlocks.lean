import ContinuousFlexibility.Analysis.N07aActualMainWeightedLift
import ContinuousFlexibility.Analysis.N07aActualScalarWeightedLift

/-!
# Genuine weighted blocks of the original N06 relative operator

The principal, potential, and all three scalar contributions are combined
in the actual volume graph. The forgotten field is the original N06
operator between its actual angular projections, including the actual
frequency difference for commutator blocks.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

local instance n07aRelativeWeightedBlocksLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aRelativeWeightedBlocksLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aRelativeWeightedBlocksUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aRelativeWeightedBlocksUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aRelativeWeightedBlocksGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aRelativeWeightedBlocksGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n07a_actualRelative_weighted_band_lift
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
        V.forget (3 / 4 : ℝ) t (b + p) W =
          V.forget (3 / 4 : ℝ) 0 b
            ((if commute then ((l : ℝ) - j) else 1) •
              n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b l
                (P.relative (liftSectorParameter S C z) F)) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (A * parameterGrading S (b + d) z *
              ‖n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U‖ +
            C₁ * (1 + parameterGrading S (b + p + d) z) * ‖F‖) := by
  obtain ⟨d₀, hmain⟩ := n07a_actualRelativeMain_weighted_band_lift hD hborder hS hT
    h01 h02 h03 h04 href hcur hprincipal hR hAux h05 h06 hI
  obtain ⟨d₁, hscalar⟩ := n07a_actualRelativeScalar_weighted_band_lift (B := B) hD hS hT
    h01 h03 h04 href hcur h05.2.1 hI
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  let d : ℕ := max d₀ d₁
  have h₀ : d₀ ≤ d := le_max_left _ _
  have h₁ : d₁ ≤ d := le_max_right _ _
  have hzref := n07a_reference_mem_stateNeighborhood h01
  have hsref := h01.2.2.1.stateSector
  have hmaps := h04.2.2.2.2.2.2.2.1 (C.referenceState, 0) hzref hsref
  have hmap (m : ℕ) : MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (physicalPieceOpen S K m) := (hmaps m).2.1
  have hsm (m : ℕ) : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (physicalPieceOpen S K m) := (hmaps m).2.2.2.2.1
  refine ⟨d, fun t p => ?_⟩
  obtain ⟨A, C₁, hA, hC₁, hbmain⟩ := hmain t p
  obtain ⟨C₂, hC₂, hbscalar⟩ := hscalar t (b + p)
  refine ⟨A, C₁ + C₂, hA, add_nonneg hC₁ hC₂, fun z hz U j l commute => ?_⟩
  let F := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
    (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
  have hF : n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F :=
    n07aAngularLevelBand_idempotent h05.2.1 (3 / 4 : ℝ) 0 hI b j _
  have hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 := by
    have h := n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j
    rw [hF] at h
    exact h.symm
  obtain ⟨W, hW, hWnorm⟩ := hbmain z hz U j l commute
  obtain ⟨Z, hZ, hZnorm⟩ := hbscalar z hz j F hU l commute
  refine ⟨W + Z, ?_, ?_⟩
  · rw [map_add, hW, hZ, map_smul, n07aAngularLevelBand_forget]
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, n07aAngularSequenceBand_apply]
    rw [← map_add, ← smul_add, n07aRelativeMainSource, sub_add_cancel, map_smul]
  · have ht : 0 ≤ n07aAngularTail ((j : ℤ) - l) := by unfold n07aAngularTail; positivity
    have hl : parameterGrading S (b + d₀) z ≤ parameterGrading S (b + d) z :=
      hmono (Nat.add_le_add_left h₀ b) z
    have hh₀ : parameterGrading S (b + p + d₀) z ≤
        1 + parameterGrading S (b + p + d) z :=
      (hmono (Nat.add_le_add_left h₀ (b + p)) z).trans (le_add_of_nonneg_left zero_le_one)
    have hh₁ : 1 + parameterGrading S (b + p + d₁) z ≤
        1 + parameterGrading S (b + p + d) z :=
      add_le_add_left (hmono (Nat.add_le_add_left h₁ (b + p)) z) 1
    have hmain' := (norm_add_le W Z).trans (add_le_add hWnorm hZnorm)
    apply hmain'.trans
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ ht
    have hlow := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hA)
      (norm_nonneg (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U))
    have hhigh₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₀ hC₁) (norm_nonneg F)
    have hhigh₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₁ hC₂) (norm_nonneg F)
    nlinarith

end ContinuousFlexibility.Analysis
