import ContinuousFlexibility.Analysis.N06PrimitivePrincipalBandLift
import ContinuousFlexibility.Analysis.N06CanonicalSourceSchur

/-!
# The actual principal relative operator on the same source space

The Schur construction realizes the genuine cubic principal difference
of the original N05 inverse.  Its source is identified on every input by
the original compact canonical tests.  The statement retains the given
K, V, b and B and does not use an N06 inverse or a pre-existing relative
operator bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06PrincipalOperatorLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrincipalOperatorLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

theorem n06_primitivePrincipal_operator_for_family
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * parameterGrading S N z ∧
        ∀ F, V.forget (3 / 4 : ℝ) 0 b (Mc F) =
          n06PrimitivePrincipalSource href hcur hI J z hz F := by
  have hV : IsVolumeModel T S K V := h.2.2.1
  obtain ⟨N, A₀, hA₀, hblocks⟩ :=
    n06_primitivePrincipal_band_lift hT hS h href hcur hprincipal hR hAux hI J
  let tailSum : ℝ := ∑' k : ℤ, n07aAngularTail k
  have htail : 0 ≤ tailSum := tsum_nonneg n07aAngularTail_nonneg
  refine ⟨N, A₀ * tailSum, mul_nonneg hA₀ htail, ?_⟩
  intro z hz
  let f := n06PrimitivePrincipalSourceLinear href hcur hI J z hz
  let Q := n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz
  have hQ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ)
      (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
      n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ) (f F m) = Q m φ hφ F :=
    n06PrimitivePrincipalSource_pairingCLM href hcur hI J z hz F m φ hφ
  have hρ : 0 ≤ parameterGrading S N z := apply_nonneg _ _
  obtain ⟨Mc, hMc, hforget⟩ := n06_canonicalSource_schur hV hI f Q hQ
    (A₀ * parameterGrading S N z) (mul_nonneg hA₀ hρ) (hblocks z hz)
  refine ⟨Mc, hMc.trans_eq ?_, hforget⟩
  dsimp only [tailSum]
  ring

theorem n06_primitivePrincipal_operator
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * parameterGrading S N z ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p *
              divergenceOperator
                (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                  (K.dividedDifference (liftSectorParameter S C z) m).a
                  (K.dividedDifference (liftSectorParameter S C z) m).b
                  (K.dividedDifference (liftSectorParameter S C z) m).c) φ p
                ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m = false → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have h05 : N05Properties D T S C K V b B := h.2
  let hI : ∀ m, K.left m < K.right m := fun m => (h04.1.referenceBounds m).2.1
  let J : N06PrimitiveReferenceJetFamily B :=
    n06PrimitiveReferenceJets hS h01 h03 h04 h05 href hprincipal
  obtain ⟨N, A, hA, hmaps⟩ :=
    n06_primitivePrincipal_operator_for_family hT hS h href hcur hprincipal hR hAux hI J
  refine ⟨N, A, hA, ?_⟩
  intro z hz
  obtain ⟨Mc, hMc, hforget⟩ := hmaps z hz
  refine ⟨Mc, hMc, ?_, ?_⟩
  · intro F m hm φ hφ
    rw [hforget F]
    calc
      _ = ∫ p, n06InverseCanonicalHeight B F m p *
          n06PrimitivePrincipalTest href hcur hI z hz m φ p ∂canonicalMeasure S K m :=
        n06PrimitivePrincipalSource_pairing href hcur hI J z hz F m hφ
      _ = _ := by
        rw [n06InverseCanonicalHeight_apply]
        apply integral_congr_ae
        filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
        rw [n06PrimitivePrincipalTest_eq_actualCubic h01 h04 href hcur hI z hz hm φ hp]
  · intro F m hm
    rw [hforget F]
    exact n06PrimitivePrincipalSource_negative href hcur hI J z hz F m
      (by simp only [hm, Bool.false_eq_true, not_false_eq_true])

end ContinuousFlexibility.Analysis
