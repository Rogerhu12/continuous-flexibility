module

public import ContinuousFlexibility.Analysis.N01RadialCoefficientMaterialInverse
public import ContinuousFlexibility.Analysis.N01ActualRootGeometry
public import ContinuousFlexibility.Analysis.RootOpticalEndpointLower
public import ContinuousFlexibility.Analysis.RootCoefficientDivision

/-!
# The actual root factor reciprocal from the component optical lower

The input is the explicit optical inequality for the same reference,
component and material host. It is not asserted to be a consequence of
the current N01 certificate. At the root, N01's actual denominator
ratios compare the speed with its reference value. The radial coefficient
inverse then gives a material reciprocal bound for the actual divided
factor. The qualitative strip radius has no inverse cost.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem rootFactor_inverse_of_relative_speed
    {a c v κ A : ℝ} (ha : 0 < a) (hv : 0 < v) (hκ : 0 < κ)
    (hvκ : κ ≤ v ^ 2) (hvc : v / 2 ≤ c) (hai : a⁻¹ ≤ A) :
    0 < a ^ 2 * c ^ 2 ∧ (a ^ 2 * c ^ 2)⁻¹ ≤ 4 * κ⁻¹ * A ^ 2 := by
  have hc : 0 < c := (half_pos hv).trans_le hvc
  have hs := pow_le_pow_left₀ (div_nonneg hv.le (by norm_num : (0 : ℝ) ≤ 2)) hvc 2
  have hκc : κ / 4 ≤ c ^ 2 := by nlinarith only [hvκ, hs]
  have hci : (c ^ 2)⁻¹ ≤ 4 * κ⁻¹ := by
    have hi := inv_anti₀ (div_pos hκ (by norm_num : (0 : ℝ) < 4)) hκc
    calc
      _ ≤ (κ / 4)⁻¹ := hi
      _ = 4 * κ⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hai2 : (a ^ 2)⁻¹ ≤ A ^ 2 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr ha.le) hai 2
  refine ⟨mul_pos (pow_pos ha 2) (pow_pos hc 2), ?_⟩
  calc
    (a ^ 2 * c ^ 2)⁻¹ = (a ^ 2)⁻¹ * (c ^ 2)⁻¹ := by
      rw [mul_inv_rev, mul_comm]
    _ ≤ A ^ 2 * (4 * κ⁻¹) :=
      mul_le_mul hai2 hci (inv_nonneg.mpr (sq_nonneg c)) (sq_nonneg A)
    _ = 4 * κ⁻¹ * A ^ 2 := by ring

/-- A raw component optical lower controls the reciprocal of the same
actual divided factor. No change of reference or material witness, and
no bound for a chosen model radius, is used. -/
theorem n01_rootFactor_axis_inverse_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε)
    (hK : 0 < K) :
    ∃ K0 P : ℝ, 0 < K0 ∧ 0 ≤ P ∧
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ t, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * t) = t * g t) →
      ∀ R : ℝ, 0 < R → ∀ z ∈ stateNeighborhood S C base ε,
        stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R → ∀ θ : ℝ,
        let G := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side)
        0 < G (0, θ) ∧ (G (0, θ))⁻¹ ≤ K0 * T.E0 (T.sample j) ^ P := by
  obtain ⟨Ka, Pa, hKa, hPa, hainv⟩ :=
    hN.originalRadialCoefficient_inverse_component_material_bound hT
  refine ⟨4 * Ka ^ 2 * K, Pa + Pa + K,
    mul_pos (mul_pos (by norm_num) (pow_pos hKa 2)) hK,
    add_nonneg (add_nonneg hPa hPa) hK.le, ?_⟩
  intro m j hhost hoptical side g hg hfactor R hR z hz hs hstrip θ
  let E := T.E0 (T.sample j)
  have hE : 0 < E :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  let κ := K⁻¹ * E ^ (-K)
  have hκ : 0 < κ := mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hE _)
  have hκinv : κ⁻¹ = K * E ^ K := by
    dsimp only [κ]
    rw [Real.rpow_neg hE.le K, mul_inv_rev, inv_inv, inv_inv]
    ring
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hpos : ∀ x ∈ Icc (C.left m) (C.right m), 0 < D.w x := by
    intro x hx
    exact hN.1.1.choose_spec.1.2.2.2.2.1 x
      ⟨hcomp.1.trans_le hx.1, hx.2.trans_lt hcomp.2.2.1⟩
  have hrcc : r ∈ Icc (C.left m) (C.right m) := by
    cases side <;>
      simp only [r, n01ComponentRoot, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
    · exact ⟨le_rfl, hcomp.2.1.le⟩
    · exact ⟨hcomp.2.1.le, le_rfl⟩
  have hroot := n01_component_root_data hN m side
  have hq : (r, θ) ∈ annularOpen D := ⟨hroot.1, mem_univ _⟩
  have hv := referenceRootSpeedFactor_lower_of_component_optical
    hN.1.1.choose_spec.1.2.2.1.1 hg
    (hN.1.1.choose_spec.1.1.trans hcomp.1) hcomp.2.1 hκ hpos side hfactor hoptical
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hprofile : stateProfile D S C z.1 r = D.w r := by
    simpa only [rootProfileShift, mul_zero, add_zero] using hdata.2.2.2.2.2.1
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs (r, θ) hq
  have hspeed := factoredCharacteristicSpeed_reference_bounds
    (wref := D.w) (g := g) (w := stateProfile D S C z.1)
    (z := stateHeight D S C z) (r := r) (σ := σ) (p := (0, θ))
    hdata.1 hdata.2.1 hdata.2.2.1
    (by simpa only [hpoint, ← hprofile] using hb.2.2.1)
    (by simpa only [hpoint, ← hprofile] using hb.2.2.2.1)
    (by simpa only [hpoint] using hb.2.2.2.2.1)
    (by simpa only [hpoint] using hb.2.2.2.2.2)
  let a := (originalCoefficients D S C z).a (r, θ)
  let c := factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ (0, θ)
  have ha : 0 < a :=
    (div_pos (hpos r hrcc) (by norm_num : (0 : ℝ) < 16)).trans_le
      (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hq)
  have hbound := rootFactor_inverse_of_relative_speed ha hv.1 hκ hv.2.1 hspeed.1
    (hainv z hz hs m j hhost (r, θ) hrcc)
  have he : rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (0, θ) = a ^ 2 * c ^ 2 := by
    simp only [rootCoefficientRadialFactor, hpoint, a, c, originalCoefficients]
  dsimp only
  change 0 < rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (0, θ) ∧ _
  rw [he]
  refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
  change 4 * κ⁻¹ * (Ka * E ^ Pa) ^ 2 = (4 * Ka ^ 2 * K) * E ^ (Pa + Pa + K)
  rw [hκinv]
  calc
    4 * (K * E ^ K) * (Ka * E ^ Pa) ^ 2 =
        (4 * Ka ^ 2 * K) * ((E ^ Pa * E ^ Pa) * E ^ K) := by ring
    _ = (4 * Ka ^ 2 * K) * E ^ (Pa + Pa + K) := by
      rw [← Real.rpow_add hE, ← Real.rpow_add hE]

end ContinuousFlexibility.Analysis
