import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootShiftPower
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketDirections
import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra

/-!
# Distributed bounds for every actual absorbed packet coordinate

The two fixed coordinates have zero positive parameter jets. The four
variable coordinates are the original quadratic height inputs. A
single interpolation base controls a fixed radial and intrinsic angular
prefix, while every further angular derivative pays only its own order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem packet_constant_parameter_bound
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {c M H P : ℝ} (J : SmoothDirections U (fun _ => c))
    (hc : |c| ≤ M) (hM : 0 ≤ M) (hH : 0 ≤ H) (hP : 1 ≤ P)
    (k : ℕ) (x : X) (hx : x ∈ U) (v : Fin k → X) :
    |J.D k x v| ≤ M * parameterHeightWeight H k * P := by
  by_cases hk : k = 0
  · subst k
    rw [smoothDirections_D_zero_apply J hx v]
    simpa only [parameterHeightWeight, ite_true, mul_one] using
      hc.trans (le_mul_of_one_le_right hM hP)
  · rw [smoothDirections_D_constant J (Nat.pos_of_ne_zero hk) hx v, abs_zero]
    exact mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH k))
      (zero_le_one.trans hP)

local instance n04PositivePacketPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The exact six-coordinate packet satisfies a common normalized
bound, including every genuine parameter tower of every mixed input. -/
theorem n04PositiveGeometry_rootPacket_finiteShift_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (x0 : AnnularState S) (N requestedBase : ℕ) :
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 6, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => mixedDerivative a (b + d)
        (fun q => n06ActualRootAbsorbedCoordinates D S z q i) p),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading (stateGrading S) realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
      (∀ j, pairGrading (stateGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (stateGrading S) realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading (stateGrading S) realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C * T.E0 p.1 ^ A *
          parameterHeightWeight (T.H p.1 ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  refine (n04PositiveGeometry_rootHeightInputs_finiteShift_power
    hD hT hS hE x0 N requestedBase).elim fun B h => ?_
  refine h.elim fun loss h => ?_
  refine h.elim fun hB hraw => ?_
  obtain ⟨L0, hL0, hheight⟩ :=
    materialHeight_E0_weight_bounded hT (γ := scalarBeta) (by norm_num [scalarBeta]) 0
  let L : ℝ := max 1 L0
  have hL : 1 ≤ L := le_max_left _ _
  obtain ⟨W, hW, hw⟩ := n06_radialLift_finite_frechet_bound (b := D.b)
    hD.choose_spec.1.1 hD.choose_spec.1.2.2.1.1.contDiffOn N
  refine ⟨B, loss, hB, fun K s => ?_⟩
  refine (hraw K s).elim fun C0 h => ?_
  refine h.elim fun A h => ?_
  refine h.elim fun hC0 h => ?_
  refine h.elim fun hA hb => ?_
  let C : ℝ := 1 + W + C0 * L
  have hprod : 0 ≤ C0 * L := mul_nonneg (zero_le_one.trans hC0) (zero_le_one.trans hL)
  have hC : 1 ≤ C := (le_add_of_nonneg_right hW).trans (le_add_of_nonneg_right hprod)
  have hC0L : C0 * L ≤ C := by dsimp only [C]; linarith only [hW]
  have hWC : W + 1 ≤ C := by
    dsimp only [C]
    linarith only [hprod]
  refine ⟨C, A, hC, hA, ?_⟩
  intro i a d had b hbs p hp U J k hk z hz hzq hzlow v hv R hR hzR hvR
  have hEn : 0 ≤ T.E0 p.1 := zero_le_one.trans (hE p.1 hp.1)
  have hEa : 1 ≤ T.E0 p.1 ^ A := Real.one_le_rpow (hE p.1 hp.1) hA
  have hH : 0 ≤ T.H p.1 ^ scalarBeta :=
    Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _
  have hHL : T.H p.1 ^ scalarBeta ≤ L := by
    have hh := hheight p.1 hp.1
    have hh' : T.H p.1 ^ scalarBeta ≤ L0 := by
      simpa only [Real.rpow_zero, mul_one] using hh
    exact hh'.trans (le_max_right _ _)
  have hPH : T.H p.1 ^ scalarBeta ≤ L * parameterHeightWeight (T.H p.1 ^ scalarBeta) k := by
    by_cases hk0 : k = 0
    · simpa only [parameterHeightWeight, if_pos hk0, mul_one] using hHL
    · simpa only [parameterHeightWeight, if_neg hk0] using
        le_mul_of_one_le_left hH hL
  have hP : 1 ≤ R ^ ((b : ℝ) / ((s : ℝ) + 1)) := Real.one_le_rpow hR (by positivity)
  have hCE : 0 ≤ C * T.E0 p.1 ^ A :=
    mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hEa)
  have hfixed (c : ℝ) (hc : |c| ≤ W + 1)
      (Jc : SmoothDirections U (fun _ => c)) :
      |Jc.D k z v| ≤ C * T.E0 p.1 ^ A *
        parameterHeightWeight (T.H p.1 ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) :=
    packet_constant_parameter_bound Jc
      ((hc.trans hWC).trans (le_mul_of_one_le_right (zero_le_one.trans hC) hEa))
      hCE hH hP k z hz v
  have hvariable (j : Fin 4)
      (Jj : SmoothDirections U (fun y => mixedDerivative a (b + d)
        (fun q => n06ActualRootAbsorbedCoordinates D S y q
          (n04PositiveGeometry_rootPacketHeightIndex j)) p)) :
      |Jj.D k z v| ≤ C * T.E0 p.1 ^ A *
        parameterHeightWeight (T.H p.1 ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
    let Jq := Jj.congr (fun y _ => n04PositiveGeometry_rootPacket_mixed_height y j a (b + d) p)
    have h := hb j a d had b hbs p hp U Jq k hk z hz hzq hzlow v hv R hR hzR hvR
    have hgain := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPH (mul_nonneg (zero_le_one.trans hC0)
        (Real.rpow_nonneg hEn A))) (Real.rpow_nonneg (zero_le_one.trans hR) _)
    have hcoeff : C0 * T.E0 p.1 ^ A * L ≤ C * T.E0 p.1 ^ A := by
      calc
        C0 * T.E0 p.1 ^ A * L = (C0 * L) * T.E0 p.1 ^ A := by ring
        _ ≤ C * T.E0 p.1 ^ A :=
          mul_le_mul_of_nonneg_right hC0L (Real.rpow_nonneg hEn A)
    have hfinish := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) ((b : ℝ) / ((s : ℝ) + 1)))
    exact h.trans (hgain.trans (by simpa only [mul_assoc] using hfinish))
  fin_cases i
  · let c := mixedDerivative a (b + d) (fun q : PolarPoint => D.w q.1) p
    have hc : |c| ≤ W + 1 := by
      by_cases hbd : b + d = 0
      · have hm := abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ
          (hD.choose_spec.1.2.2.1.1.comp contDiff_fst).contDiffOn a 0 (mem_univ p)
        have he : |c| ≤ W := by
          simpa only [c, hbd, Nat.add_zero] using
            hm.trans (hw a (by omega) p ⟨hp.1.1.le, hp.1.2.le⟩)
        exact he.trans (le_add_of_nonneg_right zero_le_one)
      · simpa only [c, mixedDerivative_radialFunction, if_neg hbd, abs_zero] using
          (show 0 ≤ W + 1 by positivity)
    let Jc : SmoothDirections U (fun _ => c) := J.congr (fun y _ => by
      apply congrArg (fun F : PolarPoint → ℝ => mixedDerivative a (b + d) F p)
      funext q
      rw [n06_actualRootAbsorbedCoordinates_eq_packet]
      rfl)
    exact hfixed c hc Jc
  · exact hvariable 0 J
  · exact hvariable 1 J
  · exact hvariable 2 J
  · exact hvariable 3 J
  · let c := mixedDerivative a (b + d) (fun _ : PolarPoint => (1 : ℝ)) p
    have hc : |c| ≤ W + 1 := by
      have hc1 : |c| ≤ 1 := by
        simp only [c, mixedDerivative, iteratedDeriv_const]
        split_ifs <;> norm_num
      exact hc1.trans (le_add_of_nonneg_left hW)
    let Jc : SmoothDirections U (fun _ => c) := J.congr (fun y _ => by
      apply congrArg (fun F : PolarPoint → ℝ => mixedDerivative a (b + d) F p)
      funext q
      rw [n06_actualRootAbsorbedCoordinates_eq_packet]
      rfl)
    exact hfixed c hc Jc

end ContinuousFlexibility.Analysis
