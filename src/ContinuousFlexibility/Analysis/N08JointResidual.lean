module

public import ContinuousFlexibility.Analysis.N08ActualScalarResidual
public import ContinuousFlexibility.Analysis.N08SectorParameterChart
public import ContinuousFlexibility.Analysis.N08CircleResidual
public import ContinuousFlexibility.Analysis.N08ReferenceFlow
public import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra

/-!
# The genuine joint residual and its scalar column

The scalar and circle fields use the same physical data. A single smaller
state neighborhood carries the actual nu derivative on the full ambient
space and the joint smooth-tame tower on the closed sector chart.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private def n08_tameDirections
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : E → F} (hf : SmoothTameOn p q U f) :
    SmoothDirections U f := Classical.choose hf

/-- Select the same rectangular neighborhood for every order of the
actual scalar tower, before specializing its projective carriers. -/
private theorem n08_uniformTameGerm_with_rectangle
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (ht : WithSeminorms p) (x0 : E)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε) {f : E × ℝ → F}
    (hf : UniformTameGerm (pairGrading p realGrading) q (x0, 0) f)
    {P : Prop}
    (hP : ∀ b : ℕ, ∀ δ : ℝ, base ≤ b → 0 < δ → δ ≤ ε →
      SmoothTameOn (pairGrading p realGrading) q
        {z : E × ℝ | p b (z.1 - x0) < δ ∧ |z.2| < δ} f → P) : P := by
  letI : IsTopologicalAddGroup E := ht.isTopologicalAddGroup
  obtain ⟨germBase, germLoss, radius, hradius, hfixed⟩ := hf
  let b := max base germBase
  let δ := min ε (radius / 2)
  have hsub : {z : E × ℝ | p b (z.1 - x0) < δ ∧ |z.2| < δ} ⊆
      {z | pairGrading p realGrading germBase (z - (x0, 0)) < radius} := by
    intro z hz
    change p germBase (z.1 - x0) + |z.2 - 0| < radius
    rw [sub_zero]
    have hx := (hp (le_max_right base germBase) (z.1 - x0)).trans_lt hz.1
    have hq := hz.2
    have hd : δ ≤ radius / 2 := min_le_right _ _
    linarith
  have hopen : IsOpen {z : E × ℝ | p b (z.1 - x0) < δ ∧ |z.2| < δ} :=
    (isOpen_lt ((ht.continuous_seminorm b).comp
      (continuous_fst.sub continuous_const)) continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const)
  exact hP b δ (le_max_left _ _) (lt_min hε (half_pos hradius))
    (min_le_left _ _) (smoothTameOn_mono hfixed.1 hopen hsub)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

def n08ResidualData
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε) :
    ResidualData S where
  scalar := n08ActualScalarResidual hT hS hN
  circle := n08CircleResidual hS hR

theorem n08ResidualData_scalar_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode ((n08ResidualData hT hS hN hR).scalar z).val p =
      scalarResidualField D S C z p :=
  n08ActualScalarResidual_decode hT hS hN hz hs p hp

theorem n08ResidualData_circle_coe
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ((n08ResidualData hT hS hN hR).circle z).val = R.residual z :=
  n08CircleResidual_coe hS hR hz hs

theorem n08ResidualData_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε) :
    jointResidual S (n08ResidualData hT hS hN hR) (C.referenceState, 0) = 0 :=
  n08_jointResidual_reference_zero hS hN hR
    (fun _ hz hs => n08ResidualData_scalar_decode hT hS hN hR hz hs)
    (fun _ hz hs => n08ResidualData_circle_coe hT hS hN hR hz hs)

private theorem n08ResidualData_smooth_of_scalar
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {b : ℕ} {δ : ℝ} (hb : base ≤ b) (hδε : δ ≤ ε)
    (hscalar : SmoothTameOn (pairGrading (stateGrading S) realGrading) S.sourceGrading
      (stateNeighborhood S C b δ) (n08ActualScalarResidual hT hS hN)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading) (residualGrading S)
      (sectorNeighborhood S b δ δ)
      (sectorJointResidual S C (n08ResidualData hT hS hN hR)) := by
  have hsector := n08_smoothTameOn_sector_pullback (C := C) hscalar
    (fun z hz => (n08_liftSectorParameter_mem S C b δ z).mpr hz)
  have hcircle := smoothTameOn_mono (n08CircleResidual_smoothTame hS hN.2.2.1 hR)
    (n08_isOpen_sectorNeighborhood S b δ δ) (n08_sectorNeighborhood_mono hb hδε hδε)
  exact smoothTameOn_prodMk_generic
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) hsector hcircle

/-- The same actual residual and nu column work on one open neighborhood;
the nu derivative is not restricted to sector directions or base points. -/
theorem n08ResidualData_nu_and_smooth
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∃ ν : AnnularState S × ℝ → S.Source,
        (∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 →
          ∀ p ∈ annularOpen D,
            (S.height (3 / 4 : ℝ)).decode (ν z).val p = nuColumnField D S C z p) ∧
        (∀ z ∈ stateNeighborhood S C b δ,
          HasProjectiveLineDerivAt
            (fun x => (n08ResidualData hT hS hN hR).scalar (x, z.2))
            (ν z) z.1 (n08NuDirection S)) ∧
        SmoothTameOn (pairGrading (sectorGrading S) realGrading) (residualGrading S)
          (sectorNeighborhood S b δ δ)
          (sectorJointResidual S C (n08ResidualData hT hS hN hR)) := by
  refine n08_uniformTameGerm_with_rectangle (solve_stateGrading_monotone S)
    (solve_stateGrading_withSeminorms S) C.referenceState base hN.2.1
    (n08ActualScalarResidual_uniformTameGerm hT hS hN) ?_
  intro b δ hb hδ hδε hscalar
  have hsubN : stateNeighborhood S C b δ ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hδε
  let J : SmoothDirections (stateNeighborhood S C b δ) (n08ActualScalarResidual hT hS hN) :=
    n08_tameDirections hscalar
  refine ⟨b, δ, hb, hδ, hδε, n08NuColumn J, ?_, ?_, ?_⟩
  · intro z hz hs p hp
    exact n08NuColumn_decode hS J
      (fun _ hy hsector => n08ActualScalarResidual_decode hT hS hN (hsubN hy) hsector)
      hz hs p hp
  · intro z hz
    exact n08NuColumn_hasLineDerivAt J hz
  · exact n08ResidualData_smooth_of_scalar hT hS hN hR hb hδε hscalar

end ContinuousFlexibility.Statements
