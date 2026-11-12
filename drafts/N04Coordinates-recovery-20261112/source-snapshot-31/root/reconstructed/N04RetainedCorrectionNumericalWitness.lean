import ContinuousFlexibility.Analysis.N01CorrectionCoefficientMaterialTame
import ContinuousFlexibility.Analysis.N01ResidualSmoothTame
import ContinuousFlexibility.Analysis.N03CorrectionAssembly
import ContinuousFlexibility.Analysis.N03SourceFromActualCoefficientJets
import ContinuousFlexibility.Analysis.ReturnCorrectionUniformNeighborhood

/-!
# Retain every numerical witness of the same correction construction

The buffered optical cutoff, its true host and material scales, the
closed-buffer coefficient bounds, and both actual flow slope bounds
are returned with the exact N02/N03 fields produced using them. There is
one invocation of the buffered construction and no second neighborhood
or collar selection after the return correction has been assembled.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance n04NumericalCorrectionStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem N01Properties.n04_exists_through03_preserving_correction_numerical_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ R : ReturnEquationData S, ∃ L : ReturnCorrectionData S,
      ∃ χ : ℕ → ℝ → ℝ, ∃ cell : ℕ → ℕ, ∃ base' : ℕ, ∃ ε' : ℝ,
        base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
          NonlinearPropertiesThrough03 D T S C R L base' loss ε' ∧
          L.coefficients = returnCorrectedCoefficients D S C χ ∧
          L.minusFlow = returnCorrectedMinusFlow S C χ ∧
          (∀ m, ContDiff ℝ ∞ (χ m)) ∧
          (∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1) ∧
          (∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
          (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
            χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1)) ∧
          (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (cell m)) ∧
          (∀ k : ℕ, ∃ B Q : ℝ, 0 ≤ B ∧ 0 ≤ Q ∧ ∀ m r,
            |iteratedDeriv k (χ m) r| ≤ B * radialE (D.cellIndex (cell m)) ^ Q) ∧
          (∀ z ∈ stateNeighborhood S C base' ε', ∀ m (p : PolarPoint),
            p.1 ∈ tsupport (deriv (χ m)) →
              0 < (originalCoefficients D S C z).b p ^ 2 -
                (originalCoefficients D S C z).a p *
                  (originalCoefficients D S C z).c p) ∧
      (∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
        0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
        (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (cell m) ∧
          0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
          (δ m)⁻¹ ≤ K * radialE (D.cellIndex (cell m)) ^ A ∧
          ∀ r ∈ Icc (x m - δ m) (x m + δ m),
            radialE (D.cellIndex (cell m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
        (∀ m, χ m = returnOpticalCutoff (x m) (δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m / 2) (x m + δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Ioo (x m - δ m) (x m + δ m)) ∧
        (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
          |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (cell m)) ^ (A * n)) ∧
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
          p.1 ∈ Icc (x m - δ m) (x m + δ m) →
          let d := lam * radialE (D.cellIndex (cell m)) ^ (-P) / 2
          0 < d ∧ d ≤ (originalCoefficients D S C z).a p ∧
          d ≤ -(originalCoefficients D S C z).c p ∧
          d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
          0 < (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧
          deriv (C.minusFlow z m r) θ ≤ 3 / 2) ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
          deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2 := by
  classical
  obtain ⟨base', ε', χ, hbase, hε', hε'ε, hN', hχdata, hendData, hcollar,
    hdiscFull, hcorrected, hflowState, hflow⟩ :=
    hN.exists_opticalCorrection_flow_buffered_uniform hS hT
  obtain ⟨j, x, δ, K, Qδ, Qopt, lam, P, hK, hQδ, hQopt, hlam, hP,
    hdata, hformula, hhalfSupport, hstripSupport, hjets, hpositive⟩ := hcollar
  obtain ⟨R, hR⟩ := hN'.exists_returnEquation hS hT
  let l : ℕ → ℝ := fun m => x m - δ m
  let h : ℕ → ℝ := fun m => x m + δ m
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) :=
    (hdata m).1
  have hl (m : ℕ) : C.left m < l m := (hdata m).2.2.1
  have hh (m : ℕ) : h m < C.right m := (hdata m).2.2.2.1
  have hχ (m : ℕ) : ContDiff ℝ ∞ (χ m) := (hχdata m).1
  have hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) →
      χ m r ∈ Icc (0 : ℝ) 1 := fun m r _ => (hχdata m).2 r
  have hsupp (m : ℕ) : Function.support (deriv (χ m)) ⊆
      Ioo (C.left m) (C.right m) :=
    (subset_tsupport _).trans (hendData m).2.2
  have hend (m : ℕ) : χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) :=
    ⟨(hendData m).1, (hendData m).2.1⟩
  have hcutoff : ∀ k : ℕ, ∃ B Q : ℝ, 0 ≤ B ∧ 0 ≤ Q ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ B * radialE (D.cellIndex (j m)) ^ Q := by
    intro k
    obtain ⟨B, hB, hbound⟩ := hjets k
    exact ⟨B, Qδ * (k : ℝ), hB.le, mul_nonneg hQδ.le (Nat.cast_nonneg k), hbound⟩
  have hdisc : ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p *
            (originalCoefficients D S C z).c p := by
    intro z hz _ m p _ hne
    exact hdiscFull z hz m p (subset_tsupport _ hne)
  have hstripDisc : ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ m (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a p *
            (originalCoefficients D S C (liftSectorParameter S C z)).c p := by
    intro z hz m p hp
    exact (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m p
      ⟨hp.1.le, hp.2.le⟩).2.2.2.2
  have hquantitative : ∀ z ∈ stateNeighborhood S C base' ε', ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        d ≤ (originalCoefficients D S C z).a p ∧
          d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p *
              (originalCoefficients D S C z).c p := by
    intro z hz m p hp
    have hd := hpositive z hz m p ⟨hp.1.le, hp.2.le⟩
    exact ⟨hd.2.1, hd.2.2.2.1⟩
  have hcoeff := hN'.returnCorrectionSmoothCoefficientJets_local_material_tame
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh
    hstripSupport hstripDisc hflow hlam hP.le hquantitative
  obtain ⟨E, hE, htame⟩ :=
    hN'.exists_returnCorrectionSource_of_actual_coefficient_bounds hS hT hR
      j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh
      hstripSupport hstripDisc hdiscFull hcoeff
  have hE' : ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ ρ η p,
      (S.height (3 / 4 : ℝ)).decode (E z ρ η).val p =
        returnCorrectionResidualErrorField D S C R χ z ρ η p := by
    intro z hz hs ρ η p
    simpa only [physicalSourceDecode_apply] using hE z hz hs ρ η p
  obtain ⟨L, hLcoefficients, hLminusFlow, _hLerror, hL⟩ :=
    hN'.n04_exists_returnCorrection_preserving_fields hR hS hT
      χ hχ hχrange hsupp hend hdiscFull hcorrected E hE' htame
  exact ⟨R, L, χ, j, base', ε', hbase, hε', hε'ε, ⟨⟨hN', hR⟩, hL⟩,
    hLcoefficients, hLminusFlow, hχ, hχrange, hsupp, hend, hcell, hcutoff, hdiscFull,
    ⟨x, δ, K, Qδ, Qopt, lam, P, hK, hQδ, hQopt, hlam, hP,
      hdata, hformula, hhalfSupport, hstripSupport, hjets, hpositive⟩, hflowState, hflow⟩

end ContinuousFlexibility.Statements
