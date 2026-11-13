import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSampleCoefficientDirections
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

local instance n04PositiveSampleCoefficientStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option diagnostics true in
set_option trace.profiler true in
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
  let driftData := n04PositiveGeometry_orientedRootTrace_finiteShift_power
    W.hT W.hS hN hεone hE N requestedBase
  let Bd : ℕ := driftData.choose
  let Ld : ℕ := driftData.choose_spec.choose
  have hBd : requestedBase ≤ Bd := driftData.choose_spec.choose_spec.1
  have hd := driftData.choose_spec.choose_spec.2
  let speedData := n04PositiveGeometry_factoredRootTrace_finiteShift_power
    W.hT W.hS hN hεone hE N requestedBase
  let Bc : ℕ := speedData.choose
  let Lc : ℕ := speedData.choose_spec.choose
  have hBc : requestedBase ≤ Bc := speedData.choose_spec.choose_spec.1
  have hc := speedData.choose_spec.choose_spec.2
  let referenceData := n04PositiveGeometry_referenceRootSpeedFactor_sample_prefix W X N
  let F : ℝ := referenceData.choose
  have hF : 1 ≤ F := referenceData.choose_spec.1
  have hFbound := referenceData.choose_spec.2
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨max Bd Bc, max Ld Lc, hBd.trans (le_max_left _ _), fun K s => ?_⟩
  let driftOrder := hd K s
  let Cd : ℝ := driftOrder.choose
  let Ad : ℝ := driftOrder.choose_spec.choose
  have hCd : 1 ≤ Cd := driftOrder.choose_spec.choose_spec.1
  have hAd : 0 ≤ Ad := driftOrder.choose_spec.choose_spec.2.1
  have hdb := driftOrder.choose_spec.choose_spec.2.2
  let speedOrder := hc K s
  let Cc : ℝ := speedOrder.choose
  let Ac : ℝ := speedOrder.choose_spec.choose
  have hCc : 1 ≤ Cc := speedOrder.choose_spec.choose_spec.1
  have hAc : 0 ≤ Ac := speedOrder.choose_spec.choose_spec.2.1
  have hcb := speedOrder.choose_spec.choose_spec.2.2
  let driftSample := n04PositiveGeometry_positiveEndpoint_parameter_weight W X
    (γ := (3 / 4 : ℝ)) (by norm_num) hAd (zero_le_one.trans hCd)
  let Dd : ℝ := driftSample.choose
  have hDd : 1 ≤ Dd := driftSample.choose_spec.1
  have hds := driftSample.choose_spec.2
  let speedSample := n04PositiveGeometry_positiveEndpoint_parameter_weight W X
    (γ := (3 / 4 : ℝ)) (by norm_num) hAc (zero_le_one.trans hCc)
  let Dc : ℝ := speedSample.choose
  have hDc : 1 ≤ Dc := speedSample.choose_spec.1
  have hcs := speedSample.choose_spec.2
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
      let π : PolarPoint →L[ℝ] ℝ := σ • ContinuousLinearMap.fst ℝ ℝ ℝ
      let JP : SmoothDirections (sectorNeighborhood W.S base ε ε)
          (fun y => iteratedDeriv (b + d) (radialBoundaryJet
            (fun q => π (n06PhysicalRootFields W.D W.S W.C
              (liftSectorParameter W.S W.C y) (rootProfileShift r σ q))) 0 a) θ) :=
        J.congr (fun y _ => congrArg
          (fun f : PolarPoint → ℝ => iteratedDeriv (b + d) (radialBoundaryJet f 0 a) θ)
          (n04PositiveGeometry_orientedDrift_eq_projection W.D W.S W.C
            (liftSectorParameter W.S W.C y) r σ))
      have hout := hdb r hr hroot σ hσ a d had π (n04PositiveGeometry_rootDrift_projection_norm hσ)
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
