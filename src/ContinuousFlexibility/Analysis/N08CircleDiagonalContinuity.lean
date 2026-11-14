module

public import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal

/-!
# Continuity of the actual diagonal entries

The diagonal uses the continuous first jet of the actual return map.
Continuity settles any finite collection of components on one common
neighborhood.  The infinite collection still requires its separate
uniform geometric estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08CircleDiagonal_value (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (m : ℕ) :
    n08CircleDiagonal hS hR z m = n08ControlMeanCoordinate S m
      ((n08CircleSectorJet hR).D 1 (n08CircleSectorPoint hS C z)
        (Fin.cons (n08_sectorProjection hS (0, 0, n08ControlBasis hS m, 0), 0) Fin.elim0)) := by
  exact congrArg (n08ControlMeanCoordinate S m)
    ((n08CircleColumn_apply hS hR z (n08ControlBasis hS m)).trans
      (n08CircleStateDerivative_apply hS hR z (0, (0, (n08ControlBasis hS m, 0)))))

theorem n08CircleDiagonal_continuousOn (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) (m : ℕ) :
    ContinuousOn (fun z => n08CircleDiagonal hS hR z m)
      {z | (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε} := by
  have hp : Continuous (n08CircleSectorPoint hS C) :=
    ((n08_sectorProjection hS).continuous.comp
      (continuous_fst.sub continuous_const)).prodMk continuous_snd
  let v : Fin 1 → StateDirections S × ℝ :=
    Fin.cons (n08_sectorProjection hS (0, 0, n08ControlBasis hS m, 0), 0) Fin.elim0
  have hj : ContinuousOn
      (fun z => (n08CircleSectorJet hR).D 1 (n08CircleSectorPoint hS C z) v)
      {z | (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε} :=
    ((n08CircleSectorJet hR).continuous 1).comp
      (hp.prodMk continuous_const).continuousOn
      (fun z hz => ⟨n08CircleSectorPoint_mem hS href hz, mem_univ v⟩)
  simpa only [n08CircleDiagonal_value] using
    (n08ControlMeanCoordinate S m).continuous.comp_continuousOn' hj

theorem n08CircleDiagonal_continuousAt_reference
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (m : ℕ) :
    ContinuousAt (fun z => n08CircleDiagonal hS hR z m) (C.referenceState, 0) := by
  have hc : Continuous (fun z : AnnularState S × ℝ => (n08_stateProjection hS z.1, z.2)) :=
    ((n08_stateProjection hS).continuous.comp continuous_fst).prodMk continuous_snd
  have href : (n08_stateProjection hS C.referenceState, 0) ∈
      stateNeighborhood S C base ε := by
    rw [n08_stateProjection_reference hS hN.2.2.1]
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      exact n08_seminorm_center_lt (stateGrading S base) C.referenceState hN.2.1
    · exact (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1
  exact (n08CircleDiagonal_continuousOn hS hN.2.2.1 hR m).continuousAt
    (((n08_isOpen_stateNeighborhood S C base ε).preimage hc).mem_nhds href)

theorem n08CircleDiagonal_finite_near_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (I : Finset ℕ) :
    ∀ᶠ z in 𝓝 (C.referenceState, (0 : ℝ)), ∀ m ∈ I,
      (1 / 2 : ℝ) ≤ |n08CircleDiagonal hS hR z m| ∧
        |n08CircleDiagonal hS hR z m| ≤ 2 := by
  apply I.eventually_all.mpr
  intro m _
  have hc : ContinuousAt (fun z : AnnularState S × ℝ =>
      |n08CircleDiagonal hS hR z m - 1|) (C.referenceState, 0) :=
    ((n08CircleDiagonal_continuousAt_reference hS hN hR m).sub
      (continuousAt_const (y := (1 : ℝ)))).abs
  have ht : Tendsto (fun z => |n08CircleDiagonal hS hR z m - 1|)
      (𝓝 (C.referenceState, (0 : ℝ))) (𝓝 0) := by
    simpa only [n08CircleDiagonal_reference hT hS hN hR, sub_self, abs_zero] using hc.tendsto
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  have hab := abs_lt.mp hz
  have hpos : 0 ≤ n08CircleDiagonal hS hR z m := by linarith only [hab.1]
  rw [abs_of_nonneg hpos]
  constructor <;> linarith only [hab.1, hab.2]

end ContinuousFlexibility.Statements
