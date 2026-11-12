import ContinuousFlexibility.Analysis.RetainedPositiveIntervalEndpointX
import ContinuousFlexibility.Analysis.ActualNegativeMaterialRatioJets
import ContinuousFlexibility.Analysis.MaterialEnvelopeRatioJets

/-!
# Actual whole-positive material ratio jets

The true whole-interval endpoint-coordinate bound is applied to the
original midpoint host sample. H and M keep their exact real powers
until the sample denominator cancels. The envelope uses its proved
scaled floor. Unit rescaling pays only a positive physical width power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- A bounded displacement controls the actual normalized H or M power,
including every physical derivative. The denominator point stays fixed. -/
theorem materialHM_normalized_physical_jets_of_bounded_X_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (useM : Bool) (γ : ℝ) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (Statements.endpointDistance D r) -
        endpointX 1 (Statements.endpointDistance D s)| ≤ L →
      |iteratedDeriv n (materialHMNormalizedPower T useM γ s) r| ≤
        B * T.E0 s ^ A := by
  let w := materialHMWeight T useM
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    materialHMWeight_rpow_physical_jet_bound hT useM γ n
  have htransfer : ∃ J P : ℝ, 0 < J ∧ 0 ≤ P ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (Statements.endpointDistance D r) -
        endpointX 1 (Statements.endpointDistance D s)| ≤ L →
      w r ^ γ * T.E0 r ^ A ≤ J * (w s ^ γ * T.E0 s ^ P) := by
    cases useM with
    | false =>
      simpa only [w, materialHMWeight, Bool.false_eq_true, ite_false,
        Real.rpow_zero, mul_one] using
        material_global_H_M_E0_rpow_bounded_X_shift hT hD γ 0 hA hL
    | true =>
      simpa only [w, materialHMWeight, ite_true, Real.rpow_zero, one_mul] using
        material_global_H_M_E0_rpow_bounded_X_shift hT hD 0 γ hA hL
  obtain ⟨J, P, hJ, hP, htransfer⟩ := htransfer
  refine ⟨B * J, P, mul_nonneg hB hJ.le, hP, ?_⟩
  intro r s hr hs hdist
  have hspos : 0 < w s := materialHMWeight_pos hT useM hs
  have hsnonneg : 0 ≤ w s ^ (-γ) := Real.rpow_nonneg hspos.le _
  have hcancel : w s ^ γ * w s ^ (-γ) = 1 := by
    rw [← Real.rpow_add hspos, add_neg_cancel, Real.rpow_zero]
  change |iteratedDeriv n (fun t => w t ^ γ * w s ^ (-γ)) r| ≤
    (B * J) * T.E0 s ^ P
  rw [iteratedDeriv_mul_const_field, abs_mul, abs_of_nonneg hsnonneg]
  calc
    _ ≤ (B * w r ^ γ * T.E0 r ^ A) * w s ^ (-γ) :=
      mul_le_mul_of_nonneg_right (hphysical r hr) hsnonneg
    _ = B * (w r ^ γ * T.E0 r ^ A) * w s ^ (-γ) := by ring
    _ ≤ B * (J * (w s ^ γ * T.E0 s ^ P)) * w s ^ (-γ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (htransfer r s hr hs hdist) hB) hsnonneg
    _ = (B * J) * (w s ^ γ * w s ^ (-γ)) * T.E0 s ^ P := by ring
    _ = (B * J) * T.E0 s ^ P := by rw [hcancel, mul_one]

/-- A selector for the three actual normalized scalar powers.
When envelope is true, useM has no effect. -/
def materialRatioNormalizedPower (T : MaterialData)
    (envelope useM : Bool) (γ sample : ℝ) : ℝ → ℝ :=
  if envelope then materialE0NormalizedPower T γ sample
  else materialHMNormalizedPower T useM γ sample

theorem materialRatio_normalized_physical_jets_of_bounded_X_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (envelope useM : Bool) (γ : ℝ) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (Statements.endpointDistance D r) -
        endpointX 1 (Statements.endpointDistance D s)| ≤ L →
      |iteratedDeriv n (materialRatioNormalizedPower T envelope useM γ s) r| ≤
        B * T.E0 s ^ A := by
  cases envelope with
  | false =>
    simpa only [materialRatioNormalizedPower, Bool.false_eq_true, ite_false] using
      materialHM_normalized_physical_jets_of_bounded_X_shift hT hD useM γ n hL
  | true =>
    simpa only [materialRatioNormalizedPower, ite_true] using
      materialE0_normalized_physical_jets_of_bounded_X_shift hT hD γ n hL

variable {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S₀ K₀ q length) (hS₀ : IsSelectedTail S₀)
  (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile)
  (hcoordinates : R11aRetainedCoordinates P Γ)
  {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  (hC : controlGeometryConditions Γ.reference S C)
  {T : MaterialData} (hT : IsMaterialData Γ.reference T)

/-- The genuine midpoint may belong to any actual host cell. Its sample
and the entire closed component are kept throughout all orders. -/
theorem retainedReference_positive_materialRatio_physical_jets
    (envelope useM : Bool) (γ : ℝ) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
          |iteratedDeriv n
            (materialRatioNormalizedPower T envelope useM γ (T.sample j)) r| ≤
              B * T.E0 (T.sample j) ^ A := by
  obtain ⟨L, hL, hdist⟩ := retainedReference_positive_midpoint_sample_X_bound
    P hS₀ hband hq hΓ hw hcoordinates hC hT
  obtain ⟨B, A, hB, hA, hjet⟩ :=
    materialRatio_normalized_physical_jets_of_bounded_X_shift
      hT hΓ.2.1 envelope useM γ n hL
  refine ⟨B, A, hB, hA, ?_⟩
  intro i j hhost r hr
  have hl := (retainedReference_positive_endpoints_interior
    P hS₀ hband hq hΓ hw hcoordinates i false).1.1
  have hu := (retainedReference_positive_endpoints_interior
    P hS₀ hband hq hΓ hw hcoordinates i true).1.2
  exact hjet r (T.sample j) ⟨hl.trans_le hr.1, hr.2.trans_lt hu⟩
    (materialSample_mem_interval hΓ.2.1 hT j) (hdist i j hhost r hr)

/-- Every angular order is zero except order zero. Physical unit
coordinates cost a positive width power bounded by the annular width. -/
theorem retainedReference_positive_materialRatio_unit_jets
    (envelope useM : Bool) (γ : ℝ) (a : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ p ∈ CanonicalGeometry.unitStrip, ∀ b : ℕ,
          |mixedDerivative a b (fun v =>
            materialRatioNormalizedPower T envelope useM γ (T.sample j)
              (n04PositiveLeft i +
                (n04PositiveRight i - n04PositiveLeft i) * v.1)) p| ≤
                  B * T.E0 (T.sample j) ^ A := by
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    retainedReference_positive_materialRatio_physical_jets
      P hS₀ hband hq hΓ hw hcoordinates hC hT envelope useM γ a
  refine ⟨|Γ.reference.b - Γ.reference.a| ^ a * B, A,
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, hA, ?_⟩
  intro i j hhost p hp b
  let f := materialRatioNormalizedPower T envelope useM γ (T.sample j)
  let d := n04PositiveLeft i
  let c := n04PositiveRight i - n04PositiveLeft i
  have hf : Continuous (deriv Γ.reference.w) :=
    hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hbnd := n04PositiveComponent_bounds hf i
  have hc : 0 < c := sub_pos.mpr hbnd.2.1
  have hwidth : c ≤ Γ.reference.b - Γ.reference.a := by
    dsimp only [c]
    linarith only [hbnd.1, hbnd.2.2]
  have hpoint : d + c * p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
    have hlow := mul_pos hc hp.1.1
    have hupp : c * p.1 < c := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hp.1.2 hc
    change d < d + c * p.1 ∧ d + c * p.1 < n04PositiveRight i
    dsimp only [d, c] at *
    constructor <;> linarith only [hlow, hupp]
  have hEs : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT j)).2.2.1
  change |mixedDerivative a b (fun v => f (d + c * v.1)) p| ≤ _
  rw [n08_mixedDerivative_radial (fun r => f (d + c * r))]
  by_cases hb : b = 0
  · rw [if_pos hb, n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
    have hpow : |c| ^ a ≤ |Γ.reference.b - Γ.reference.a| ^ a := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_of_pos hc]
      exact hwidth.trans (le_abs_self _)
    have hvalue := hphysical i j hhost (d + c * p.1) ⟨hpoint.1.le, hpoint.2.le⟩
    calc
      _ ≤ |c| ^ a * (B * T.E0 (T.sample j) ^ A) :=
        mul_le_mul_of_nonneg_left hvalue (pow_nonneg (abs_nonneg _) _)
      _ ≤ |Γ.reference.b - Γ.reference.a| ^ a * (B * T.E0 (T.sample j) ^ A) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hB (Real.rpow_nonneg hEs.le _))
      _ = _ := by ring
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hB)
      (Real.rpow_nonneg hEs.le _)

end ContinuousFlexibility.Analysis
