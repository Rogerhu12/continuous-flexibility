module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootShiftPower
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketDirections
public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra

/-!
# Distributed bounds for every actual absorbed packet coordinate

The two fixed coordinates have zero positive parameter jets. The four
variable coordinates are the original quadratic height inputs. A
single interpolation base controls a fixed radial and intrinsic angular
prefix, while every further angular derivative pays only its own order.
-/

@[expose] public section

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

private theorem packet_prefix_of_height
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (pgrade : ℕ → Seminorm ℝ Y) (F : Fin 4 → Y → PolarPoint → ℝ)
    (packet : Y × ℝ → PolarPoint → Fin 6 → ℝ)
    (w : ℝ → ℝ) (hwSmooth : ContDiff ℝ ∞ w)
    (Ω : Set PolarPoint) (E H : PolarPoint → ℝ)
    (hE : ∀ q ∈ Ω, 1 ≤ E q) (hHsource : ∀ q ∈ Ω, 0 ≤ H q)
    (hfixed0 : ∀ z q, packet z q 0 = w q.1)
    (hfixed5 : ∀ z q, packet z q 5 = 1)
    (hpacketVariable : ∀ z j a b q,
      mixedDerivative a b (fun t => packet z t (n04PositiveGeometry_rootPacketHeightIndex j)) q =
        z.2 * mixedDerivative a b (F j z.1) q)
    (x0 : Y) (B loss N K s : ℕ) (C0 A L W : ℝ)
    (hC0 : 1 ≤ C0) (hA : 0 ≤ A) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hHbound : ∀ q ∈ Ω, H q ≤ L)
    (hw : ∀ a, a ≤ N → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ a (fun p : PolarPoint => w p.1) q‖ ≤ W)
    (hb : ∀ i : Fin 4, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ q ∈ Ω, ∀ U : Set (Y × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a (b + d) (F i z.1) q),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading pgrade realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (Y × ℝ),
      (∀ j, pairGrading pgrade realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading pgrade realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading pgrade realGrading (s + loss) (v j) ≤ R) →
      |J.D k z v| ≤ C0 * E q ^ A * H q * R ^ ((b : ℝ) / ((s : ℝ) + 1))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ i : Fin 6, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ q ∈ Ω, ∀ U : Set (Y × ℝ),
      ∀ J : SmoothDirections U (fun z => mixedDerivative a (b + d) (fun t => packet z t i) q),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading pgrade realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (Y × ℝ),
      (∀ j, pairGrading pgrade realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading pgrade realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading pgrade realGrading (s + loss) (v j) ≤ R) →
      |J.D k z v| ≤ C * E q ^ A * parameterHeightWeight (H q) k *
        R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  let C : ℝ := 1 + W + C0 * L
  have hprod : 0 ≤ C0 * L := mul_nonneg (zero_le_one.trans hC0) (zero_le_one.trans hL)
  have hC : 1 ≤ C := (le_add_of_nonneg_right hW).trans (le_add_of_nonneg_right hprod)
  have hC0L : C0 * L ≤ C := by dsimp only [C]; linarith only [hW]
  have hWC : W + 1 ≤ C := by
    dsimp only [C]
    linarith only [hprod]
  refine ⟨C, hC, ?_⟩
  intro i a d had b hbs p hp U J k hk z hz hzq hzlow v hv R hR hzR hvR
  have hEn : 0 ≤ E p := zero_le_one.trans (hE p hp)
  have hEa : 1 ≤ E p ^ A := Real.one_le_rpow (hE p hp) hA
  have hH : 0 ≤ H p := hHsource p hp
  have hHL : H p ≤ L := hHbound p hp
  have hPH : H p ≤ L * parameterHeightWeight (H p) k := by
    by_cases hk0 : k = 0
    · simpa only [parameterHeightWeight, if_pos hk0, mul_one] using hHL
    · simpa only [parameterHeightWeight, if_neg hk0] using
        le_mul_of_one_le_left hH hL
  have hP : 1 ≤ R ^ ((b : ℝ) / ((s : ℝ) + 1)) := Real.one_le_rpow hR (by positivity)
  have hCE : 0 ≤ C * E p ^ A :=
    mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hEa)
  have hfixed (c : ℝ) (hc : |c| ≤ W + 1)
      (Jc : SmoothDirections U (fun _ => c)) :
      |Jc.D k z v| ≤ C * E p ^ A *
        parameterHeightWeight (H p) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) :=
    packet_constant_parameter_bound Jc
      ((hc.trans hWC).trans (le_mul_of_one_le_right (zero_le_one.trans hC) hEa))
      hCE hH hP k z hz v
  have hvariable (j : Fin 4)
      (Jj : SmoothDirections U (fun y => mixedDerivative a (b + d)
        (fun q => packet y q
          (n04PositiveGeometry_rootPacketHeightIndex j)) p)) :
      |Jj.D k z v| ≤ C * E p ^ A *
        parameterHeightWeight (H p) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
    let Jq := Jj.congr (fun y _ => hpacketVariable y j a (b + d) p)
    have h := hb j a d had b hbs p hp U Jq k hk z hz hzq hzlow v hv R hR hzR hvR
    have hgain := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPH (mul_nonneg (zero_le_one.trans hC0)
        (Real.rpow_nonneg hEn A)))
          (Real.rpow_nonneg (zero_le_one.trans hR) ((b : ℝ) / ((s : ℝ) + 1)))
    have hcoeff : C0 * E p ^ A * L ≤ C * E p ^ A := by
      calc
        C0 * E p ^ A * L = (C0 * L) * E p ^ A := by ring
        _ ≤ C * E p ^ A :=
          mul_le_mul_of_nonneg_right hC0L (Real.rpow_nonneg hEn A)
    have hfinish := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) ((b : ℝ) / ((s : ℝ) + 1)))
    exact h.trans (hgain.trans (by simpa only [mul_assoc] using hfinish))
  fin_cases i
  · let c := mixedDerivative a (b + d) (fun q : PolarPoint => w q.1) p
    have hc : |c| ≤ W + 1 := by
      by_cases hbd : b + d = 0
      · have hm := abs_mixedDerivative_le_norm_iteratedFDeriv
          (f := fun q : PolarPoint => w q.1) isOpen_univ
          (by simpa only [Function.comp_def] using
            (hwSmooth.comp contDiff_fst).contDiffOn) a 0 (mem_univ p)
        have he : |c| ≤ W := by
          simpa only [c, hbd, Nat.add_zero] using
            hm.trans (hw a (by omega) p hp)
        exact he.trans (le_add_of_nonneg_right zero_le_one)
      · simpa only [c, mixedDerivative_radialFunction, if_neg hbd, abs_zero] using
          (show 0 ≤ W + 1 by positivity)
    let Jc : SmoothDirections U (fun _ => c) := J.congr (fun y _ => by
      apply congrArg (fun F : PolarPoint → ℝ => mixedDerivative a (b + d) F p)
      funext q
      exact hfixed0 y q)
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
      exact hfixed5 y q)
    exact hfixed c hc Jc

private def packetFiniteShiftPowerBound
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (pgrade : ℕ → Seminorm ℝ Y)
    (packet : Y × ℝ → PolarPoint → Fin 6 → ℝ)
    (Ω : Set PolarPoint) (E H : PolarPoint → ℝ)
    (x0 : Y) (N requestedBase : ℕ) : Prop :=
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 6, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ p ∈ Ω, ∀ U : Set (Y × ℝ),
      ∀ J : SmoothDirections U (fun z => mixedDerivative a (b + d)
        (fun q => packet z q i) p),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading pgrade realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (Y × ℝ),
      (∀ j, pairGrading pgrade realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading pgrade realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading pgrade realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C * E p ^ A * parameterHeightWeight (H p) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1))

private theorem packetFiniteShiftPower_of_height
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (pgrade : ℕ → Seminorm ℝ Y) (F : Fin 4 → Y → PolarPoint → ℝ)
    (packet : Y × ℝ → PolarPoint → Fin 6 → ℝ)
    (w : ℝ → ℝ) (hwSmooth : ContDiff ℝ ∞ w)
    (Ω : Set PolarPoint) (E H : PolarPoint → ℝ)
    (hE : ∀ q ∈ Ω, 1 ≤ E q) (hH : ∀ q ∈ Ω, 0 ≤ H q)
    (hfixed0 : ∀ z q, packet z q 0 = w q.1)
    (hfixed5 : ∀ z q, packet z q 5 = 1)
    (hvariable : ∀ z j a b q,
      mixedDerivative a b (fun t => packet z t (n04PositiveGeometry_rootPacketHeightIndex j)) q =
        z.2 * mixedDerivative a b (F j z.1) q)
    (x0 : Y) (N requestedBase : ℕ) (L W : ℝ) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hheight : ∀ q ∈ Ω, H q ≤ L)
    (hw : ∀ a, a ≤ N → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ a (fun p : PolarPoint => w p.1) q‖ ≤ W)
    (hraw : N04PositiveGeometryRootHeightFiniteShiftPowerBound
      pgrade F Ω E H x0 N requestedBase) :
    packetFiniteShiftPowerBound pgrade packet Ω E H x0 N requestedBase := by
  refine hraw.elim fun B h => ?_
  refine h.elim fun loss h => ?_
  refine h.elim fun hB hraw => ?_
  refine ⟨B, loss, hB, fun K s => ?_⟩
  refine (hraw K s).elim fun C0 h => ?_
  refine h.elim fun A h => ?_
  refine h.elim fun hC0 h => ?_
  refine h.elim fun hA hb => ?_
  refine (packet_prefix_of_height pgrade F packet w hwSmooth Ω E H hE hH
    hfixed0 hfixed5 hvariable x0 B loss N K s C0 A L W hC0 hA hL hW
    hheight hw hb).elim fun C h => ?_
  exact ⟨C, A, h.1, hA, h.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The exact six-coordinate packet satisfies a common normalized
bound, including every genuine parameter tower of every mixed input.
The transparent statement is assembled over an abstract state space to
avoid repeatedly elaborating the physical grading instances. -/
theorem n04PositiveGeometry_rootPacket_finiteShift_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (x0 : AnnularState S) (N requestedBase : ℕ) :
    packetFiniteShiftPowerBound (Y := AnnularState S) (stateGrading S)
      (n06ActualRootAbsorbedCoordinates D S) (annularOpen D)
      (fun q => T.E0 q.1) (fun q => T.H q.1 ^ scalarBeta) x0 N requestedBase := by
  let hheightExists :=
    materialHeight_E0_weight_bounded hT (γ := scalarBeta) (by norm_num [scalarBeta]) 0
  let L0 : ℝ := hheightExists.choose
  have hheight := hheightExists.choose_spec.2
  let L : ℝ := max 1 L0
  have hL : 1 ≤ L := le_max_left _ _
  let hradialExists := n06_radialLift_finite_frechet_bound (b := D.b)
    hD.choose_spec.1.1 hD.choose_spec.1.2.2.1.1.contDiffOn N
  let W : ℝ := hradialExists.choose
  have hW := hradialExists.choose_spec.1
  have hw := hradialExists.choose_spec.2
  refine packetFiniteShiftPower_of_height (Y := AnnularState S) (stateGrading S)
    (fun j x => n06RootNormalizedHeightFields D S x.1 j)
    (n06ActualRootAbsorbedCoordinates D S) D.w hD.choose_spec.1.2.2.1.1
    (annularOpen D) (fun q => T.E0 q.1) (fun q => T.H q.1 ^ scalarBeta)
    (fun q hq => hE q.1 hq.1)
    (fun q hq => Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _)
    (fun z q => by rw [n06_actualRootAbsorbedCoordinates_eq_packet]; rfl)
    (fun z q => by rw [n06_actualRootAbsorbedCoordinates_eq_packet]; rfl)
    (fun z j a b q => n04PositiveGeometry_rootPacket_mixed_height z j a b q)
    x0 N requestedBase L W hL hW
    (fun q hq => (show T.H q.1 ^ scalarBeta ≤ L0 from by
      calc
        T.H q.1 ^ scalarBeta = T.H q.1 ^ scalarBeta * T.E0 q.1 ^ (0 : ℝ) := by
          rw [Real.rpow_zero, mul_one]
        _ ≤ L0 := hheight q.1 hq.1).trans (le_max_right _ _))
    (fun a ha q hq => hw a ha q ⟨hq.1.1.le, hq.1.2.le⟩)
    ?_
  exact n04PositiveGeometry_rootHeightInputs_finiteShift_power hD hT hS hE x0 N requestedBase

end ContinuousFlexibility.Analysis
