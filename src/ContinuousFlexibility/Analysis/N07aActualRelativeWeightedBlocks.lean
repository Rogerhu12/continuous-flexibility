module

public import ContinuousFlexibility.Analysis.N07aActualMainWeightedLift
public import ContinuousFlexibility.Analysis.N07aActualScalarWeightedLift

/-!
# Genuine weighted blocks of the original N06 relative operator

The principal, potential, and all three scalar contributions are combined
in the actual volume graph. The forgotten field is the original N06
operator between its actual angular projections, including the actual
frequency difference for commutator blocks.
-/

@[expose] public section

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

private theorem n07a_relativeWeightedBlocks_add_sub_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] F) (κ : ℝ) (u v : E) :
    Q (κ • (u - v)) + Q (κ • v) = κ • Q u := by
  rw [← map_add, ← smul_add, sub_add_cancel, map_smul]

private theorem n07a_relativeWeightedBlocks_join_forget
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (t : ℝ) (s l : ℕ) (κ : ℝ)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (W Z : V.level (3 / 4 : ℝ) t s)
    (hW : V.forget (3 / 4 : ℝ) t s W = (fun m =>
      n07aAngularBand m (hI m) l
        (κ • n07aRelativeMainSource (P := P) href hcur z hz F m (hI m))))
    (hZ : V.forget (3 / 4 : ℝ) t s Z = (fun m =>
      n07aAngularBand m (hI m) l
        (κ • n07aRelativeScalarPart href hcur z hz m (hI m) (B.inverse F).val.1))) :
    V.forget (3 / 4 : ℝ) t s (W + Z) =
      V.forget (3 / 4 : ℝ) 0 b
        (κ • n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b l
          (P.relative (liftSectorParameter S C z) F)) := by
  have hband := n07aAngularLevelBand_forget hV (3 / 4 : ℝ) 0 hI b l
    (P.relative (liftSectorParameter S C z) F)
  have htarget := (map_smul (V.forget (3 / 4 : ℝ) 0 b) κ
    (n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b l
      (P.relative (liftSectorParameter S C z) F))).trans
    (congrArg (fun f : CanonicalSequence S K => κ • f) hband)
  have hsum := congrArg₂ (fun f g : CanonicalSequence S K => f + g) hW hZ
  refine (map_add (V.forget (3 / 4 : ℝ) t s) W Z).trans
    (hsum.trans ((funext fun m => ?_).trans htarget.symm))
  simp only [Pi.add_apply, Pi.smul_apply, n07aAngularSequenceBand_apply]
  exact n07a_relativeWeightedBlocks_add_sub_map (n07aAngularBand m (hI m) l) κ
    (V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m)
    (n07aRelativeScalarPart href hcur z hz m (hI m) (B.inverse F).val.1)

private theorem n07a_relativeWeightedBlocks_join_norm
    {E : Type*} [NormedAddCommGroup E] (W Z : E)
    (τ A C₁ C₂ ρ₀ ρ₁ η₀ η₁ η₂ x y : ℝ)
    (hτ : 0 ≤ τ) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hl : ρ₀ ≤ ρ₁) (hh₀ : η₀ ≤ η₂) (hh₁ : η₁ ≤ η₂)
    (hW : ‖W‖ ≤ τ * (A * ρ₀ * x + C₁ * η₀ * y))
    (hZ : ‖Z‖ ≤ τ * (C₂ * η₁ * y)) :
    ‖W + Z‖ ≤ τ * (A * ρ₁ * x + (C₁ + C₂) * η₂ * y) := by
  have hlow := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hA) hx
  have hhigh₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₀ hC₁) hy
  have hhigh₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₁ hC₂) hy
  calc
    ‖W + Z‖ ≤ ‖W‖ + ‖Z‖ := norm_add_le W Z
    _ ≤ τ * (A * ρ₀ * x + C₁ * η₀ * y) + τ * (C₂ * η₁ * y) := add_le_add hW hZ
    _ = τ * (A * ρ₀ * x + C₁ * η₀ * y + C₂ * η₁ * y) := by ring
    _ ≤ τ * (A * ρ₁ * x + C₁ * η₂ * y + C₂ * η₂ * y) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hlow hhigh₀) hhigh₁) hτ
    _ = _ := by ring

theorem n07a_actualRelative_weighted_band_lift
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hI : ∀ m, K.left m < K.right m) :
    ∃ d : ℕ, ∀ t : ℝ, ∀ p : ℕ, ∃ A C₁ : ℝ, 0 ≤ A ∧ 0 ≤ C₁ ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∀ U : V.level (3 / 4 : ℝ) 0 (b + p), ∀ (j l : ℕ) (commute : Bool),
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
  let main := n07a_actualRelativeMain_weighted_band_lift hD hborder hS hT
    h01 h02 h03 h04 href hcur hprincipal hR hAux h05 h06 hI
  let d₀ : ℕ := main.choose
  have hmain := main.choose_spec
  let scalar := n07a_actualRelativeScalar_weighted_band_lift (B := B) hD hS hT
    h01 h03 h04 href hcur hRatio h05.2.1 hI
  let d₁ : ℕ := scalar.choose
  have hscalar := scalar.choose_spec
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  let d : ℕ := max d₀ d₁
  have h₀ : d₀ ≤ d := le_max_left _ _
  have h₁ : d₁ ≤ d := le_max_right _ _
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
  let A : ℝ := (hmain t p).choose
  let C₁ : ℝ := (hmain t p).choose_spec.choose
  have hA : 0 ≤ A := (hmain t p).choose_spec.choose_spec.1
  have hC₁ : 0 ≤ C₁ := (hmain t p).choose_spec.choose_spec.2.1
  have hbmain := (hmain t p).choose_spec.choose_spec.2.2
  let C₂ : ℝ := (hscalar t (b + p)).choose
  have hC₂ : 0 ≤ C₂ := (hscalar t (b + p)).choose_spec.1
  have hbscalar := (hscalar t (b + p)).choose_spec.2
  refine ⟨A, C₁ + C₂, hA, add_nonneg hC₁ hC₂, fun z hz U j l commute => ?_⟩
  let F : V.level (3 / 4 : ℝ) 0 b := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j
    (n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) 0 (Nat.le_add_right b p) U)
  have hF : n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F :=
    n07aAngularLevelBand_idempotent h05.2.1 (3 / 4 : ℝ) 0 hI b j _
  have hU : n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 := by
    have h := n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j
    exact h.symm.trans (congrArg (fun G : V.level (3 / 4 : ℝ) 0 b =>
      (B.inverse G).val.1) hF)
  let mainLift := hbmain z hz U j l commute
  let W : V.level (3 / 4 : ℝ) t (b + p) := mainLift.choose
  have hW := mainLift.choose_spec.1
  have hWnorm := mainLift.choose_spec.2
  let scalarLift := hbscalar z hz j F hU l commute
  let Z : V.level (3 / 4 : ℝ) t (b + p) := scalarLift.choose
  have hZ := scalarLift.choose_spec.1
  have hZnorm := scalarLift.choose_spec.2
  refine ⟨W + Z, ?_, ?_⟩
  · exact n07a_relativeWeightedBlocks_join_forget h05.2.1 href hcur hI t (b + p) l
      (if commute then ((l : ℝ) - j) else 1) z hz F W Z hW hZ
  · have ht : 0 ≤ n07aAngularTail ((j : ℤ) - l) := n07aAngularTail_nonneg _
    have hl : parameterGrading S (b + d₀) z ≤ parameterGrading S (b + d) z :=
      hmono (Nat.add_le_add_left h₀ b) z
    have hh₀ : parameterGrading S (b + p + d₀) z ≤
        1 + parameterGrading S (b + p + d) z :=
      (hmono (Nat.add_le_add_left h₀ (b + p)) z).trans (le_add_of_nonneg_left zero_le_one)
    have hh₁ : 1 + parameterGrading S (b + p + d₁) z ≤
        1 + parameterGrading S (b + p + d) z :=
      add_le_add le_rfl (hmono (Nat.add_le_add_left h₁ (b + p)) z)
    exact n07a_relativeWeightedBlocks_join_norm W Z (n07aAngularTail ((j : ℤ) - l)) A C₁ C₂
      (parameterGrading S (b + d₀) z) (parameterGrading S (b + d) z)
      (parameterGrading S (b + p + d₀) z) (1 + parameterGrading S (b + p + d₁) z)
      (1 + parameterGrading S (b + p + d) z)
      ‖n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI (b + p) j U‖ ‖F‖
      ht hA hC₁ hC₂ (norm_nonneg _) (norm_nonneg _) hl hh₀ hh₁ hWnorm hZnorm

end ContinuousFlexibility.Analysis
