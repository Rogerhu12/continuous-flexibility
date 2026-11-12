import ContinuousFlexibility.Analysis.N06PrimitivePrincipalWeightedBudget
import ContinuousFlexibility.Analysis.N07aAngularSequenceBandLift
import ContinuousFlexibility.Analysis.N07aVolumeLinearLift

/-!
# Every actual principal block belongs to the original source level

The graph consists of the genuine weak angular derivatives and the
original even reflection.  A single outer L2 majorant supplies all of its
coordinates.  No a priori bounded relative operator is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06BandLiftLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06BandLiftLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

theorem n06_primitivePrincipal_band_lift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j l
        (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h.2.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      ∃ G : V.level (3 / 4 : ℝ) 0 b,
        V.forget (3 / 4 : ℝ) 0 b G =
          n07aAngularSequenceBand hI l
            (n06PrimitivePrincipalSource href hcur hI J z hz F) ∧
        ‖G‖ ≤ A * parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * ‖F‖ := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have h05 : N05Properties D T S C K V b B := h.2
  have hD : IsAccumulatingProfile D := h01.1.1
  have hV : IsVolumeModel T S K V := h05.2.1
  obtain ⟨N, A, hA, hbudget⟩ :=
    n06_primitivePrincipal_weighted_budget hT hS h href hcur hprincipal hR hAux hI J
  refine ⟨N, A, hA, ?_⟩
  intro z hz j l F hF
  obtain ⟨a, ha, hanorm, hpiece⟩ := hbudget z hz j F hF
  let κ : ℝ := parameterGrading S N z * n07aAngularTail ((j : ℤ) - l)
  have hκ : 0 ≤ κ := mul_nonneg (apply_nonneg _ _) (n07aAngularTail_nonneg _)
  let v : lp (fun _ : ℕ => ℝ) 2 := κ • a
  have hv (m : ℕ) : ‖v m‖ = κ * a m := by
    simp only [v, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hκ (ha m))]
  let f := n06PrimitivePrincipalSource href hcur hI J z hz F
  have hf (m : ℕ) : n07aAngularReflection m (f m) = f m :=
    n06PrimitivePrincipalSource_reflection hT hS h01 h03 h04 h05
      href hcur hI J z hz F m
  have hbound (m : ℕ) : (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq b l) *
      ‖n07aAngularBand m (hI m) l (f m)‖ ≤ ‖v m‖ := by
    rw [hv]
    exact hpiece m l
  let G := n07aAngularSequenceBandLift hD hT hV (3 / 4 : ℝ) 0 hI b l f hf v hbound
  refine ⟨G, n07aAngularSequenceBandLift_forget hD hT hV
    (3 / 4 : ℝ) 0 hI b l f hf v hbound, ?_⟩
  calc
    ‖G‖ ≤ ‖v‖ := n07aAngularSequenceBandLift_norm_le hD hT hV
      (3 / 4 : ℝ) 0 hI b l f hf v hbound
    _ = κ * ‖a‖ := by rw [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
    _ ≤ κ * (A * ‖F‖) := mul_le_mul_of_nonneg_left hanorm hκ
    _ = _ := by dsimp only [κ]; ring

end ContinuousFlexibility.Analysis
