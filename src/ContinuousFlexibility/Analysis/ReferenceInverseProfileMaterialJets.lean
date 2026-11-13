import ContinuousFlexibility.Analysis.MaterialPointRadialPolynomial
import ContinuousFlexibility.Analysis.MaterialEndpointWeightTransport
import ContinuousFlexibility.Analysis.RetainedPositiveIntervalEndpointX
import ContinuousFlexibility.Radial.ReferenceCellL2
import ContinuousFlexibility.Radial.CentralStatementBridges
import ContinuousFlexibility.Radial.MorseChainScales

/-!
# Actual reciprocal-profile jets at the retained positive sample

The inverse profile is bounded on genuine radial cells, including every
finite derivative order. The actual partition first chooses a cell at
the evaluation point. The retained positive interval then transports
its point envelope to the original midpoint sample. No compact bound
for the reciprocal profile at the ambient endpoints is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped BigOperators ContDiff

/-- The accumulating-profile cell estimates give a single material
envelope for a finite prefix, uniformly over the entire open annulus. -/
theorem material_inverseProfile_finite_point_jets
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (N : ℕ) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ r ∈ radialCore D,
      ∀ k, k ≤ N → |iteratedDeriv k (fun x => (D.w x)⁻¹) r| ≤
        K * T.E0 r ^ P := by
  let C : ℕ → ℝ := hRef.choose
  have hdata : AccumulatingProfileBounds D C := hRef.choose_spec
  rcases hdata with ⟨_, hpart, hC, _, _, _, _, _, _, hinv, _⟩
  let A : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), C k
  have hA : 1 ≤ A :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hC k).le)
  have hCA (k : ℕ) (hk : k ≤ N) : C k ≤ A :=
    (Finset.single_le_sum (fun j _ => (hC j).le)
      (Finset.mem_range.mpr (by omega : k < N + 1))).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨K, P, hK, hP, hpower⟩ :=
    materialCell_radialE_power_bound hT hRef (zero_le_one.trans hA)
  refine ⟨A * K, P, mul_pos (zero_lt_one.trans_le hA) hK, hP, ?_⟩
  intro r hr k hk
  obtain ⟨j, hj⟩ := hpart.exists_localizer_ne_zero hr
  have hcell : r ∈ D.cells j := hpart.2.2.1 j hj
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (radialQ_nonneg _)
  have hraw : |iteratedDeriv k (fun x => (D.w x)⁻¹) r| ≤
      C k * radialE (D.cellIndex j) ^ C k := by
    simpa only [radialJet_eq_iteratedDeriv] using hinv j r hcell k
  calc
    _ ≤ C k * radialE (D.cellIndex j) ^ C k := hraw
    _ ≤ A * radialE (D.cellIndex j) ^ A :=
      mul_le_mul (hCA k hk)
        (Real.rpow_le_rpow_of_exponent_le hE (hCA k hk))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
    _ ≤ A * (K * T.E0 r ^ P) :=
      mul_le_mul_of_nonneg_left (hpower j r hcell) (zero_le_one.trans hA)
    _ = (A * K) * T.E0 r ^ P := by ring

/-- All points of the same closed positive component use its original
midpoint sample. The constants precede the component, host and point. -/
theorem retainedReference_positive_inverseProfile_finite_sample_jets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions Γ.reference S C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) (N : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i), ∀ k, k ≤ N →
        |iteratedDeriv k (fun x => (Γ.reference.w x)⁻¹) r| ≤
          K * T.E0 (T.sample j) ^ A := by
  obtain ⟨L, hL, hdist⟩ := retainedReference_positive_midpoint_sample_X_bound
    P hSelected hband hq hΓ hw hcoordinates hC hT
  obtain ⟨K, R, hK, hR, hpoint⟩ :=
    material_inverseProfile_finite_point_jets hT hΓ.2.1 N
  obtain ⟨J, A, hJ, hA, hshift⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hΓ.2.1 0 0 hR hL
  refine ⟨K * J, A, mul_pos hK hJ, hA, ?_⟩
  intro i j hhost r hr k hk
  have hl := (retainedReference_positive_endpoints_interior
    P hSelected hband hq hΓ hw hcoordinates i false).1.1
  have hu := (retainedReference_positive_endpoints_interior
    P hSelected hband hq hΓ hw hcoordinates i true).1.2
  have hcore : r ∈ radialCore Γ.reference :=
    ⟨hl.trans_le hr.1, hr.2.trans_lt hu⟩
  have htransfer : T.E0 r ^ R ≤ J * T.E0 (T.sample j) ^ A := by
    simpa only [Real.rpow_zero, one_mul] using hshift r (T.sample j) hcore
      (materialSample_mem_interval hΓ.2.1 hT j) (hdist i j hhost r hr)
  exact (hpoint r hcore k hk).trans
    ((mul_le_mul_of_nonneg_left htransfer hK.le).trans_eq (by ring))

end ContinuousFlexibility.Analysis
