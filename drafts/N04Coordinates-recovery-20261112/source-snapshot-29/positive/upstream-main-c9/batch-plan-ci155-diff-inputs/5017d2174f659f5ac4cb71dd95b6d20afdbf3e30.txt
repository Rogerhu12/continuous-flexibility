import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerAlgebra
import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison

/-!
# Actual cell samples for endpoint-weighted raw bounds

The physical point weight is transferred to the original component's
prescribed material sample. The exact height exponent is preserved.
The endpoint power on the coefficient factors costs only a fixed annular
width constant at each spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem mixedPowerBounds_to_componentSamples
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hC : controlGeometryConditions D S C)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {f : X → PolarPoint → ℝ}
    (hf : MixedPowerBounds p center base loss U (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1) f) :
    EndpointMixedPowerBounds p center base loss U
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m))) (fun _ => f) := by
  intro K s
  obtain ⟨Cf, Af, hCf, hAf, hb⟩ := hf K s
  obtain ⟨C0, A0, hC0, hA0, hzero⟩ :=
    materialCell_weight_comparison hT hRef 0 Af
  obtain ⟨C1, A1, hC1, hA1, hpositive⟩ :=
    materialCell_weight_comparison hT hRef (3 / 4 : ℝ) Af
  let CW : ℝ := 1 + C0 + C1
  let AW : ℝ := A0 + A1
  let L : ℝ := max 1 (D.b - D.a)
  have hCW : 1 ≤ CW := by dsimp only [CW]; linarith
  have hAW : 0 ≤ AW := add_nonneg hA0.le hA1.le
  have hL : 1 ≤ L := le_max_left _ _
  have hCF : 1 ≤ Cf * CW * L ^ s := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCf hCW) (one_le_pow₀ hL)
  refine ⟨Cf * CW * L ^ s, AW, hCF, hAW, ?_⟩
  intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  have hcell := hloc m hq.1
  have hP : RadialPartition D := hRef.choose_spec.2.1
  have hcore : q.1 ∈ Ioo D.a D.b := hP.2.2.2.1 (C.cell m) hcell
  have hsample := materialSample_mem_radialCore hT hP (C.cell m)
  have hEs : 1 ≤ T.E0 (T.sample (C.cell m)) := hE _ hsample
  have hHs : 0 ≤ T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 _ hsample).2.1.le _
  have hw : T.E0 q.1 ^ Af * parameterHeightWeight (T.H q.1 ^ (3 / 4 : ℝ)) k ≤
      CW * T.E0 (T.sample (C.cell m)) ^ AW *
        parameterHeightWeight (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) k := by
    by_cases hk0 : k = 0
    · have h0 : T.E0 q.1 ^ Af ≤ C0 * T.E0 (T.sample (C.cell m)) ^ A0 := by
        simpa only [Real.rpow_zero, mul_one, one_mul] using (hzero (C.cell m) q.1 hcell).1
      have h0' : C0 * T.E0 (T.sample (C.cell m)) ^ A0 ≤
          CW * T.E0 (T.sample (C.cell m)) ^ AW :=
        mul_le_mul (by dsimp only [CW]; linarith)
          (Real.rpow_le_rpow_of_exponent_le hEs (le_add_of_nonneg_right hA1.le))
          (Real.rpow_nonneg (zero_le_one.trans hEs) _) (zero_le_one.trans hCW)
      simpa only [parameterHeightWeight, if_pos hk0, mul_one] using h0.trans h0'
    · have h1 := (hpositive (C.cell m) q.1 hcell).1
      have h1' :
          C1 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ A1 ≤
          CW * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ AW :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (by dsimp only [CW]; linarith) hHs)
          (Real.rpow_le_rpow_of_exponent_le hEs (le_add_of_nonneg_left hA0.le))
          (Real.rpow_nonneg (zero_le_one.trans hEs) _)
          (mul_nonneg (zero_le_one.trans hCW) hHs)
      simpa only [parameterHeightWeight, if_neg hk0, mul_assoc, mul_left_comm, mul_comm]
        using h1.trans h1'
  let d : ℝ := min (q.1 - C.left m) (C.right m - q.1)
  have hd : 0 ≤ d := le_min (sub_nonneg.mpr hq.1.1.le) (sub_nonneg.mpr hq.1.2.le)
  have hdL : d ≤ L := by
    have hleft := (hC.1 m).1
    have hright := (hC.1 m).2.2
    have hh : d ≤ q.1 - C.left m := min_le_left _ _
    exact (show d ≤ D.b - D.a by linarith [hq.1.2]).trans (le_max_right _ _)
  have hdpow : d ^ a ≤ L ^ s :=
    (pow_le_pow_left₀ hd hdL a).trans
      (pow_le_pow_right₀ hL (by omega))
  have hraw := hb k hk a b hab q ⟨hcore, mem_univ _⟩ J x hx hlow v hv
    R hR hhigh hvhigh
  have hraw' : ‖J.D k x v‖ ≤
      Cf * (CW * T.E0 (T.sample (C.cell m)) ^ AW *
        parameterHeightWeight (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) k) *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (zero_le_one.trans hCf))
      (Real.rpow_nonneg (zero_le_one.trans hR) (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)))
    exact hraw.trans (by simpa only [mul_assoc] using hh)
  calc
    _ ≤ L ^ s * ‖J.D k x v‖ := mul_le_mul_of_nonneg_right hdpow (norm_nonneg _)
    _ ≤ L ^ s *
        (Cf * (CW * T.E0 (T.sample (C.cell m)) ^ AW *
          parameterHeightWeight (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) k) *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hraw' (pow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
