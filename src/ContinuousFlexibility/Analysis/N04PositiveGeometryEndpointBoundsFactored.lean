import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOrientation

/-!
# The literal factored speed with its fixed reference material cost

Only a finite list of ordinary jets of the fixed reference speed enters
the radial Leibniz rule. All parameter derivatives belong to the actual
physical coefficient, so the original height factor is retained once.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

local instance n04PositiveFactoredStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

theorem n04PositiveGeometry_factoredRootTrace_formula
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (σ : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (a : ℕ) (θ : ℝ) :
    radialBoundaryJet (factoredCharacteristicSpeed D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z)) r σ) 0 a θ =
      ∑ j : Fin (a + 1), (a.choose j : ℝ) *
        iteratedDeriv j (referenceRootSpeedFactor D.w g r σ) 0 *
        radialBoundaryJet (fun p =>
          (n06PhysicalRootFields D S C (liftSectorParameter S C z)
            (rootProfileShift r σ p)).2) 0 (a - j) θ := by
  let A : ℝ → ℝ := referenceRootSpeedFactor D.w g r σ
  let f : ℝ → ℝ := fun x =>
    (n06PhysicalRootFields D S C (liftSectorParameter S C z)
      (rootProfileShift r σ (x, θ))).2
  have hw : ContDiff ℝ ∞ D.w := hN.1.1.choose_spec.1.2.2.1.1
  have hrpos : 0 < r + σ * 0 := by
    simpa only [mul_zero, add_zero] using hN.1.1.choose_spec.1.1.trans hr.1
  have hwpos : 0 < D.w (r + σ * 0) := by
    simpa only [mul_zero, add_zero] using hN.1.1.choose_spec.1.2.2.2.2.1 r hr
  have hA : ContDiffAt ℝ ∞ A 0 :=
    contDiffAt_referenceRootSpeedFactor hw hg hrpos hwpos hg0
  have hf : ContDiffAt ℝ ∞ f 0 := by
    have h := (n06_physicalRootFields_contDiffAt_root hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) hr hroot θ).snd
    have hs : ContDiffAt ℝ ∞
        (fun x : ℝ => ((r + σ * x, θ) : PolarPoint)) 0 :=
      (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).prodMk contDiffAt_const
    have h' : ContDiffAt ℝ ∞
        (fun p => (n06PhysicalRootFields D S C (liftSectorParameter S C z) p).2)
        (r + σ * 0, θ) := by simpa only [mul_zero, add_zero] using h
    exact h'.comp 0 hs
  have hwline : ContinuousAt (fun x : ℝ => D.w (r + σ * x)) 0 :=
    hw.continuous.continuousAt.comp
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt)
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, 0 < D.w (r + σ * x) :=
    hwline.eventually (Ioi_mem_nhds hwpos)
  have he : (fun x => factoredCharacteristicSpeed D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z)) r σ (x, θ)) =ᶠ[𝓝 0]
      (fun x => A x * f x) := by
    filter_upwards [hnear] with x hx
    exact (n06_factoredRootFields_eq_physical D S C
      (liftSectorParameter S C z) g r σ (x, θ) hx.ne').2
  change iteratedDeriv a _ 0 = _
  rw [he.iteratedDeriv_eq a]
  have hmul := iteratedDeriv_fun_mul
    (hA.of_le (show (a : ℕ∞ω) ≤ ∞ by simp))
    (hf.of_le (show (a : ℕ∞ω) ≤ ∞ by simp))
  rw [Fin.sum_univ_eq_sum_range (fun j => (a.choose j : ℝ) *
    iteratedDeriv j A 0 * iteratedDeriv (a - j) f 0) (a + 1)]
  exact hmul

theorem n04PositiveGeometry_factoredRootTrace_finiteShift_power
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ r ∈ radialCore D, deriv D.w r = 0 →
      ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 →
      ∀ F : ℝ, 0 ≤ F →
      (∀ j : ℕ, j ≤ N → |iteratedDeriv j (referenceRootSpeedFactor D.w g r σ) 0| ≤ F) →
      ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => iteratedDeriv (b + d) (radialBoundaryJet
          (factoredCharacteristicSpeed D.w g
            (stateProfile D S C (liftSectorParameter S C z).1)
            (stateHeight D S C (liftSectorParameter S C z)) r σ) 0 a) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections S × ℝ),
      (∀ j, pairGrading (sectorGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading S) realGrading (s + inputLoss) z ≤ R →
      (∀ j, pairGrading (sectorGrading S) realGrading (s + inputLoss) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ F * C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let data := n04PositiveGeometry_orientedRootTrace_finiteShift_power
    hT hS hN hε hE N requestedBase
  let B : ℕ := data.choose
  let inputLoss : ℕ := data.choose_spec.choose
  have hB : requestedBase ≤ B := data.choose_spec.choose_spec.1
  have hp := data.choose_spec.choose_spec.2
  refine ⟨B, inputLoss, hB, fun K s => ?_⟩
  let orderData := hp K s
  let C0 : ℝ := orderData.choose
  let A : ℝ := orderData.choose_spec.choose
  have hC0 : 1 ≤ C0 := orderData.choose_spec.choose_spec.1
  have hA : 0 ≤ A := orderData.choose_spec.choose_spec.2.1
  have hb := orderData.choose_spec.choose_spec.2.2
  have hpow : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  refine ⟨(2 : ℝ) ^ N * C0, A, one_le_mul_of_one_le_of_one_le hpow hC0, hA, ?_⟩
  intro r hr hroot σ hσ g hg hg0 F hF hFjets a d had b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let coeff (j : Fin (a + 1)) : ℝ := (a.choose j : ℝ) *
    iteratedDeriv j (referenceRootSpeedFactor D.w g r σ) 0
  let raw (j : Fin (a + 1)) := n04Realization_orientedRootFieldTrace_joint
    hT hS hN hε hr hroot σ (ContinuousLinearMap.snd ℝ ℝ ℝ) (a - j)
  let Ji (j : Fin (a + 1)) := smoothDirections_postcompCLM (raw j)
    (coeff j • ContinuousLinearMap.id ℝ ℝ)
  have heq : EqOn (fun y => ∑ j : Fin (a + 1), coeff j * radialBoundaryJet
      (fun p => (n06PhysicalRootFields D S C (liftSectorParameter S C y.1)
        (rootProfileShift r σ p)).2) 0 (a - j) y.2)
      (fun y => radialBoundaryJet (factoredCharacteristicSpeed D.w g
        (stateProfile D S C (liftSectorParameter S C y.1).1)
        (stateHeight D S C (liftSectorParameter S C y.1)) r σ) 0 a y.2)
      (sectorNeighborhood S base ε ε ×ˢ univ) := by
    intro y hy
    exact (n04PositiveGeometry_factoredRootTrace_formula hT hS hN hr hroot
      σ g hg hg0 y.1 hy.1 a y.2).symm
  let M : ℝ := C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
    R ^ ((b : ℝ) / ((s : ℝ) + 1))
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
      (Real.rpow_nonneg (zero_le_one.trans (hE r hr)) _))
      (parameterHeightWeight_nonneg (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) k))
    (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hterm (j : Fin (a + 1)) :
      ‖(smoothDirections_angularStateSlice (Ji j) (b + d) θ).D k z v‖ ≤
        (a.choose j : ℝ) * F * M := by
    let JR := smoothDirections_angularStateSlice (raw j) (b + d) θ
    let JT := smoothDirections_angularStateSlice (Ji j) (b + d) θ
    have hraw : ‖JR.D k z v‖ ≤ M := hb r hr hroot σ hσ (a - j) d
      (by omega) (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      b hbs θ JR k hk z hz hzlow v hv R hR hzR hvR
    have hscalar := n04PositiveGeometry_parameter_constMul_bound JR JT (coeff j)
      (fun _ _ => by simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, iteratedDeriv_const_mul_field])
      k z hz v hraw
    have hcoeff : |coeff j| ≤ (a.choose j : ℝ) * F := by
      rw [coeff, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hFjets j (by omega)) (Nat.cast_nonneg _)
    exact hscalar.trans (mul_le_mul_of_nonneg_right hcoeff hM)
  have hout := n04PositiveGeometry_angularFiniteSum_parameter_bound Ji
    (sectorNeighborhood_isOpen S base ε ε) heq k (b + d) z hz θ v J
      (fun j => (a.choose j : ℝ) * F * M) hterm
  have hchoose : (∑ j : Fin (a + 1), (a.choose j : ℝ)) = (2 : ℝ) ^ a := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (a.choose j : ℝ)) (a + 1)]
    exact_mod_cast Nat.sum_range_choose a
  have hout' : ‖J.D k z v‖ ≤ (2 : ℝ) ^ a * F * M := by
    simpa only [← Finset.sum_mul, hchoose] using hout
  exact hout'.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show a ≤ N by omega)) hF) hM).trans_eq (by dsimp only [M]; ring))

end ContinuousFlexibility.Analysis
