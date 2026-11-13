import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsFactored
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootSpeedFactor
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSamplePrefix

/-!
# Actual root coefficients at one supplied positive sample

The drift and factored speed use the same original state domain. Their
finite radial and intrinsic angular prefixes have one low base before
all parameter orders. Both endpoints retain their supplied source and
their original midpoint sample, including the complete height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_rootRawCoefficient (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (g : ℝ → ℝ) (r σ : ℝ) (speed : Bool)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  if speed then factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  else orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ

theorem n04PositiveGeometry_orientedDrift_eq_projection
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r σ : ℝ) :
    orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ =
      (fun p => (σ • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (n06PhysicalRootFields D S C z (rootProfileShift r σ p))) := by
  funext p
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.fst_apply, smul_eq_mul,
    n06PhysicalRootFields, orientedCharacteristicDrift]

private theorem rootDrift_projection_norm {σ : ℝ} (hσ : |σ| ≤ 1) :
    ‖σ • ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul hσ (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
    (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

local instance n04PositiveSampleCoefficientStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootRawCoefficientTrace_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (σ : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (speed : Bool) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun y => radialBoundaryJet (n04PositiveGeometry_rootRawCoefficient
        D S C g r σ speed (liftSectorParameter S C y.1)) 0 a y.2) := by
  cases speed with
  | false =>
      apply (n04Realization_orientedRootFieldTrace_joint hT hS hN hε hr hroot σ
        (σ • ContinuousLinearMap.fst ℝ ℝ ℝ) a).congr
      intro y _
      exact congrArg (fun f : PolarPoint → ℝ => radialBoundaryJet f 0 a y.2)
        (n04PositiveGeometry_orientedDrift_eq_projection D S C
          (liftSectorParameter S C y.1) r σ).symm
  | true => exact n04Realization_factoredRootSpeedTrace_joint
      hT hS hN hε hr hroot σ g hg hg0 a

theorem n04PositiveGeometry_rootRawCoefficient_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
      ∀ ρ : ℝ, 0 < ρ →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) ρ →
      ∀ speed : Bool, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => iteratedDeriv (b + d) (radialBoundaryJet
          (n04PositiveGeometry_rootRawCoefficient W.D W.S W.C g
            (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) speed
            (liftSectorParameter W.S W.C z)) 0 a) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ j, pairGrading (sectorGrading W.S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (s + inputLoss) z ≤ R →
      (∀ j, pairGrading (sectorGrading W.S) realGrading (s + inputLoss) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
          parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hE : ∀ r ∈ radialCore W.D, 1 ≤ W.T.E0 r := fun r _ => W.floor r
  obtain ⟨Bd, Ld, hBd, hd⟩ := n04PositiveGeometry_orientedRootTrace_finiteShift_power
    W.hT W.hS hN hεone hE N requestedBase
  obtain ⟨Bc, Lc, hBc, hc⟩ := n04PositiveGeometry_factoredRootTrace_finiteShift_power
    W.hT W.hS hN hεone hE N requestedBase
  obtain ⟨F, hF, hFbound⟩ := n04PositiveGeometry_referenceRootSpeedFactor_sample_prefix W X N
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨max Bd Bc, max Ld Lc, hBd.trans (le_max_left _ _), fun K s => ?_⟩
  obtain ⟨Cd, Ad, hCd, hAd, hdb⟩ := hd K s
  obtain ⟨Cc, Ac, hCc, hAc, hcb⟩ := hc K s
  obtain ⟨Dd, hDd, hds⟩ := n04PositiveGeometry_positiveEndpoint_parameter_weight W X
    (γ := (3 / 4 : ℝ)) (by norm_num) hAd (zero_le_one.trans hCd)
  obtain ⟨Dc, hDc, hcs⟩ := n04PositiveGeometry_positiveEndpoint_parameter_weight W X
    (γ := (3 / 4 : ℝ)) (by norm_num) hAc (zero_le_one.trans hCc)
  obtain ⟨A₀, _, hpack⟩ := coefficientEnvelope_pack (F * Dc) (F + Dc)
  let A : ℝ := max Dd (max 1 A₀)
  have hA : 1 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hDdA : Dd ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro i side m hm g hg hg0 hfactor ρ hρ hstrip speed a d had b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let r := n01ComponentRoot W.C m (!side)
  let σ := n01ComponentRootOrientation (!side)
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let Q : ℝ := R ^ ((b : ℝ) / ((s : ℝ) + 1))
  have hEpos : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hQ : 0 ≤ Q := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hrad : r = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : r ∈ radialCore W.D := by
    rw [hrad]
    exact (W.roots i side).1
  have hroot : deriv W.D.w r = 0 := by
    rw [hrad]
    exact (W.roots i side).2.1
  have hσ : |σ| ≤ 1 := by cases side <;> norm_num [σ, n01ComponentRootOrientation]
  have hdpoint : Cd * W.T.E0 r ^ Ad * parameterHeightWeight (W.T.H r ^ scalarBeta) k ≤
      Dd * E ^ Dd * parameterHeightWeight H k := by
    rw [hrad]
    exact hds i side k
  have hcpoint : Cc * W.T.E0 r ^ Ac * parameterHeightWeight (W.T.H r ^ scalarBeta) k ≤
      Dc * E ^ Dc * parameterHeightWeight H k := by
    rw [hrad]
    exact hcs i side k
  have hdcost : Dd * E ^ Dd ≤ A * E ^ A := mul_le_mul hDdA
    (Real.rpow_le_rpow_of_exponent_le hEpos hDdA)
    (Real.rpow_nonneg (zero_le_one.trans hEpos) _) (zero_le_one.trans hA)
  have hccost : (F * E ^ F) * (Dc * E ^ Dc) ≤ A * E ^ A := by
    calc
      _ = (F * Dc) * E ^ (F + Dc) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hEpos)]
        ring
      _ ≤ A₀ * E ^ A₀ := hpack E hEpos
      _ ≤ A * E ^ A := mul_le_mul hA₀A
        (Real.rpow_le_rpow_of_exponent_le hEpos hA₀A)
        (Real.rpow_nonneg (zero_le_one.trans hEpos) _) (zero_le_one.trans hA)
  cases speed with
  | false =>
      let π := σ • ContinuousLinearMap.fst ℝ ℝ ℝ
      let JP := J.congr (fun y _ => congrArg
        (fun f : PolarPoint → ℝ => iteratedDeriv (b + d) (radialBoundaryJet f 0 a) θ)
        (n04PositiveGeometry_orientedDrift_eq_projection W.D W.S W.C
          (liftSectorParameter W.S W.C y) r σ))
      have hout := hdb r hr hroot σ hσ a d had π (rootDrift_projection_norm hσ)
        b hbs θ JP k hk z hz ((hp (le_max_left Bd Bc) z).trans hzlow)
        v (fun j => (hp (le_max_left Bd Bc) (v j)).trans (hv j)) R hR
        ((hp (Nat.add_le_add_left (le_max_left Ld Lc) s) z).trans hzR)
        (fun j => (hp (Nat.add_le_add_left (le_max_left Ld Lc) s) (v j)).trans (hvR j))
      exact hout.trans ((mul_le_mul_of_nonneg_right hdpoint hQ).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdcost (parameterHeightWeight_nonneg hH k)) hQ))
  | true =>
      have hFE : 0 ≤ F * E ^ F := mul_nonneg (zero_le_one.trans hF)
        (Real.rpow_nonneg (zero_le_one.trans hEpos) _)
      have hout := hcb r hr hroot σ hσ g hg hg0 (F * E ^ F) hFE
        (fun j hj => hFbound i side m hm g hg hfactor ρ hρ hstrip j hj)
        a d had b hbs θ J k hk z hz ((hp (le_max_right Bd Bc) z).trans hzlow)
        v (fun j => (hp (le_max_right Bd Bc) (v j)).trans (hv j)) R hR
        ((hp (Nat.add_le_add_left (le_max_right Ld Lc) s) z).trans hzR)
        (fun j => (hp (Nat.add_le_add_left (le_max_right Ld Lc) s) (v j)).trans (hvR j))
      have hm : (F * E ^ F) * (Cc * W.T.E0 r ^ Ac *
          parameterHeightWeight (W.T.H r ^ scalarBeta) k) ≤
          (A * E ^ A) * parameterHeightWeight H k := by
        exact (mul_le_mul_of_nonneg_left hcpoint hFE).trans
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hccost (parameterHeightWeight_nonneg hH k))
      calc
        _ ≤ (F * E ^ F) * Cc * W.T.E0 r ^ Ac *
            parameterHeightWeight (W.T.H r ^ scalarBeta) k * Q := hout
        _ = ((F * E ^ F) * (Cc * W.T.E0 r ^ Ac *
            parameterHeightWeight (W.T.H r ^ scalarBeta) k)) * Q := by ring
        _ ≤ ((A * E ^ A) * parameterHeightWeight H k) * Q :=
          mul_le_mul_of_nonneg_right hm hQ
        _ = _ := by rfl

end ContinuousFlexibility.Analysis
