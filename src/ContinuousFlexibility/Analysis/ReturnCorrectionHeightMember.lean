module

public import ContinuousFlexibility.Analysis.MaterialDivergenceEnergy
public import ContinuousFlexibility.Analysis.ReturnCorrectionTraceFlux
public import ContinuousFlexibility.Analysis.ReturnOpticalCorrectionSource
public import ContinuousFlexibility.Analysis.ReturnCoefficientGlobalWeighted

/-!
# The actual independent residual error belongs to the physical height space

The trace cutoff has been removed by a global identity of the actual
fluxes. All weighted material jets then follow from the original
height-space input, bounded actual coefficient jets, and the exact
physical derivative identities. The collar corollary supplies those
coefficient bounds from the actual N01 flow and its actual inverses.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

section ActualMember

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN hS hT hz hsector hχ hχrange hsupp hend hdisc

theorem N01Properties.returnCorrectionResidualErrorField_memLp_of_coefficient_bounds
    (ρ : CircleSpace S) (η : HeightPair S)
    (hbound : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) p‖ ≤ K)
    (a b c : ℕ) :
    MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c
      (returnCorrectionResidualErrorField D S C R χ z ρ η))
      2 materialCylinderMeasure := by
  let A (p : PolarPoint) : ℝ × ℝ := returnCorrectionCoefficientError D S C R χ z p ρ
  let u : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode η.1
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hA : ContDiffOn ℝ ∞ A (annularOpen D) := by
    intro p hp
    exact (hN.returnCorrectionCoefficientError_contDiffAt_of_cutoffs
      hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ p hp).contDiffWithinAt
  have hAb (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n (fun q => (A q).1) p‖ ≤ K := by
    obtain ⟨K, hK, hb⟩ := hbound n
    exact ⟨K, hK, fun p hp =>
      (norm_iteratedFDeriv_pair_projections_le hU hA n hp).1.trans (hb p hp)⟩
  have hBb (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n (fun q => (A q).2) p‖ ≤ K := by
    obtain ⟨K, hK, hb⟩ := hbound n
    exact ⟨K, hK, fun p hp =>
      (norm_iteratedFDeriv_pair_projections_le hU hA n hp).2.trans (hb p hp)⟩
  have hu : HeightMember D T (3 / 4 : ℝ) u := (hS.1 _).2.2.2.1 η.1
  have hLp := memLp_weightedPhysicalJet_symmetric_divergence
    hT hA.fst hA.snd hAb hBb hu.1 hu.2.2.2.2 a b c
  have heq : EqOn (returnCorrectionResidualErrorField D S C R χ z ρ η)
      (fun p => radialPartial (fun q => (A q).1 * angularPartial u q) p +
        angularPartial (fun q => (A q).1 * radialPartial u q + (A q).2 * angularPartial u q) p)
      (annularOpen D) := fun p hp =>
    hN.returnCorrectionResidualErrorField_eq_decoded_divergence hS R χ z ρ η p hp
  rw [weightedPhysicalJet_eq_of_eqOn_annularOpen hT heq a b c]
  exact hLp

theorem N01Properties.returnCorrectionResidualErrorField_heightMember_of_coefficient_bounds
    (ρ : CircleSpace S) (η : HeightPair S)
    (hbound : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) p‖ ≤ K) :
    HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η) :=
  (hN.returnCorrectionResidualErrorField_heightMember_iff
    hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η).mpr
    (hN.returnCorrectionResidualErrorField_memLp_of_coefficient_bounds
      hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η hbound)

end ActualMember

theorem N01Properties.returnCorrectionResidualErrorField_heightMember_of_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, χ m r ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    {lam P₀ B₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀) (hB₀ : 0 < B₀)
    (hlower : ∀ m : ℕ, ∀ p : PolarPoint,
      p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      lam * radialE (D.cellIndex (j m)) ^ (-P₀) ≤
        (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)
    (hinverse : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv k (C.minusReturnInverse z m) θ| ≤ A)
    (ρ : CircleSpace S) (η : HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η) := by
  have hsupp' (m : ℕ) : Function.support (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m) :=
    (subset_tsupport _).trans (hsupp m)
  have hsuppI (m : ℕ) : Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m) := by
    intro r hr
    exact ⟨(hinside m).1.trans_le (hsupp' m hr).1,
      (hsupp' m hr).2.trans_lt (hinside m).2⟩
  have hdisc (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ tsupport (deriv (χ m))) :
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)).trans_le
      (hlower m p (hsupp m hp))
  exact hN.returnCorrectionResidualErrorField_heightMember_of_coefficient_bounds
    hS hT R hz hsector χ hχ (fun m r _ => hχrange m r) hsuppI hend hdisc ρ η
    (fun n => hN.returnCorrectionCoefficientError_uniform_fderiv_bound_of_collar
      hS hT R hz hsector j x δ hδ hcell hinside χ hχ hχrange hsupp' hend
      hlam hP₀ hlower hB₀ hspeed hcutoff hflow hinverse ρ n)

end ContinuousFlexibility.Statements
