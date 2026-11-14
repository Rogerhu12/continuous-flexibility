module

public import ContinuousFlexibility.Analysis.N04bOpticalCutoffData
public import ContinuousFlexibility.Analysis.N04bOriginalType
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Source and flow inputs from the same actual optical cutoff

The actual half-width cutoff lies strictly inside its retained wider
positive collar. That whole open collar has the quantitative coefficient
lower bounds from the optical construction, including states outside the
sector. The same cutoff retains the strict corrected gap after shrinking.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

namespace N04bOpticalCutoffData

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)

def stripLeft (m : ℕ) : ℝ := Q.center m - 2 * Q.width m

def stripRight (m : ℕ) : ℝ := Q.center m + 2 * Q.width m

theorem stripLeft_gt (m : ℕ) : C.left m < Q.stripLeft m :=
  Q.buffer_left m

theorem stripRight_lt (m : ℕ) : Q.stripRight m < C.right m :=
  Q.buffer_right m

theorem strip_subset (m : ℕ) :
    Ioo (Q.stripLeft m) (Q.stripRight m) ⊆ Ioo (C.left m) (C.right m) :=
  fun _ hp => ⟨(Q.stripLeft_gt m).trans hp.1, hp.2.trans (Q.stripRight_lt m)⟩

theorem strip_support (m : ℕ) :
    tsupport (deriv (Q.cutoff m)) ⊆ Ioo (Q.stripLeft m) (Q.stripRight m) := by
  intro r hr
  have h := Q.cutoff_support m hr
  constructor
  · dsimp [stripLeft]
    linarith only [h.1, Q.width_pos m]
  · dsimp [stripRight]
    linarith only [h.2, Q.width_pos m]

theorem tsupport_interior (m : ℕ) :
    tsupport (deriv (Q.cutoff m)) ⊆ Ioo (C.left m) (C.right m) :=
  (Q.strip_support m).trans (Q.strip_subset m)

theorem support_interior (m : ℕ) :
    Function.support (deriv (Q.cutoff m)) ⊆ Ioo (C.left m) (C.right m) :=
  (subset_tsupport _).trans (Q.tsupport_interior m)

theorem endpoint_germs (m : ℕ) :
    Q.cutoff m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      Q.cutoff m =ᶠ[𝓝 (C.right m)] (fun _ => 1) :=
  ⟨Q.cutoff_left m, Q.cutoff_right m⟩

theorem range_on_component (m : ℕ) (r : ℝ)
    (_hr : r ∈ Icc (C.left m) (C.right m)) : Q.cutoff m r ∈ Icc (0 : ℝ) 1 :=
  Q.cutoff_range m r

theorem derivative_bounds : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (Q.cutoff m) r| ≤ A * radialE (D.cellIndex (Q.cell m)) ^ P := by
  intro k
  obtain ⟨K, hK, hbound⟩ := Q.cutoff_jets k
  exact ⟨K, Q.widthPower * k, hK.le,
    mul_nonneg Q.widthPower_pos.le (Nat.cast_nonneg k), hbound⟩

theorem discriminant_on_support
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ tsupport (deriv (Q.cutoff m))) :
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
  (Q.collar_positive z hz m p (Q.cutoff_support m hp)).2.2.2.2

theorem active_discriminant
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (_hs : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (_hp : p.1 ∈ Ioo (C.left m) (C.right m)) (hχ : deriv (Q.cutoff m) p.1 ≠ 0) :
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
  Q.discriminant_on_support z hz m p (subset_tsupport _ hχ)

theorem strip_discriminant
    {T : MaterialData} {loss : ℕ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (Q.stripLeft m) (Q.stripRight m)) :
    0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
      (originalCoefficients D S C (liftSectorParameter S C z)).a p *
        (originalCoefficients D S C (liftSectorParameter S C z)).c p :=
  (hN.n04b_original_negative_type hS hT
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m (Q.strip_subset m hp)).2

/-- The quantitative lower bound holds on the entire chosen open strip,
with the same constants for every state in the full neighborhood. -/
theorem strip_positive
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (Q.stripLeft m) (Q.stripRight m)) :
    let d := Q.discScale * radialE (D.cellIndex (Q.cell m)) ^ (-Q.discPower) / 2
    d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
  Q.buffer_positive z hz m p ⟨hp.1.le, hp.2.le⟩

include Q in
theorem sector_flow_slope
    {T : MaterialData} {loss : ℕ}
    (hN : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2 :=
  Q.flow_slope (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m r hr θ

theorem discriminant_lower
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (Q.center m - Q.width m) (Q.center m + Q.width m)) :
    (Q.discScale / 2) ^ 2 * radialE (D.cellIndex (Q.cell m)) ^ (-(2 * Q.discPower)) ≤
      (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  have hpow : radialE (D.cellIndex (Q.cell m)) ^ (-(2 * Q.discPower)) =
      (radialE (D.cellIndex (Q.cell m)) ^ (-Q.discPower)) ^ 2 := by
    have hE : 0 < radialE (D.cellIndex (Q.cell m)) := Real.exp_pos _
    rw [pow_two, ← Real.rpow_add hE]
    congr 1
    ring
  have hscale : (Q.discScale / 2) ^ 2 *
      radialE (D.cellIndex (Q.cell m)) ^ (-(2 * Q.discPower)) =
      (Q.discScale * radialE (D.cellIndex (Q.cell m)) ^ (-Q.discPower) / 2) ^ 2 := by
    rw [hpow]
    ring
  exact hscale.trans_le (Q.collar_positive z hz m p hp).2.2.2.1

theorem corrected_flow
    {T : MaterialData} {loss : ℕ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    returnCorrectedMinusFlow S C Q.cutoff z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => returnCorrectedMinusFlow S C Q.cutoff z m r θ)
      (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt
      (fun s => returnCorrectedMinusFlow S C Q.cutoff z m s θ)
      (minusCharacteristicSpeed (returnCorrectedCoefficients D S C Q.cutoff z)
        (r, returnCorrectedMinusFlow S C Q.cutoff z m r θ)) r) ∧
    rightChartCandidate S C z m
      (returnCorrectedMinusFlow S C Q.cutoff z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m
      (-returnCorrectedMinusFlow S C Q.cutoff z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m :=
  hN.returnCorrectedFlow_properties_of_physical hS hT hz hs Q.cutoff m
    (Q.cutoff_smooth m) (Q.range_on_component m)
    (Q.cutoff_left m).eq_of_nhds (Q.cutoff_right m).eq_of_nhds
    (fun r hr t => (Q.corrected_speeds z hz hs m r hr t).2) θ

end N04bOpticalCutoffData

end ContinuousFlexibility.Statements
