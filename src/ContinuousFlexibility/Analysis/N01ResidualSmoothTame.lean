module

public import ContinuousFlexibility.Analysis.N01ResidualSectorCoordinates
public import ContinuousFlexibility.Analysis.N01CircleLinearTame
public import ContinuousFlexibility.Analysis.CirclePositiveInverseSmoothTame
public import ContinuousFlexibility.Analysis.TameTopologicalComposition
public import ContinuousFlexibility.Analysis.TameProductDirections
public import ContinuousFlexibility.Analysis.N02ReturnAssembly

/-!
# Full smooth tameness and N02 for the actual return residual

The realized return displacement has a genuine fixed-loss tower.
Two inverse-composition maps, the actual chart coordinate, and the even
and odd continuous projections now give the frozen residual map itself.
The construction works on the full original sector neighborhood and
provides every field and every clause of N02 without an additional
membership, differentiability, or tame assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01ResidualSmoothTameStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

private theorem residual_sectorPair_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (pairGrading (sectorGrading S) realGrading) := by
  have hr : WithSeminorms realGrading := by
    apply (norm_withSeminorms ℝ ℝ).congr
    · intro n
      exact ⟨{()}, 1, by simp [realGrading]⟩
    · intro u
      exact ⟨{0}, 1, by simp [realGrading]⟩
  exact withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S) hr

private theorem smoothTameOn_circle_sub
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {H : CircleModelData} [∀ n, CompleteSpace (H.level n)]
    {p : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (ht : WithSeminorms p) {U : Set E} (hU : IsOpen U)
    {f g : E → H.Space}
    (hf : SmoothTameOn p H.grading U f) (hg : SmoothTameOn p H.grading U g) :
    SmoothTameOn p H.grading U (fun x => f x - g x) := by
  let L : H.Space × H.Space →L[ℝ] H.Space :=
    ContinuousLinearMap.fst ℝ H.Space H.Space - ContinuousLinearMap.snd ℝ H.Space H.Space
  have hL : IsTameLinear (pairGrading H.grading H.grading) H.grading L.toLinearMap 0 0 := by
    intro s hs
    refine ⟨1, fun z => ?_⟩
    change H.grading s (z.1 - z.2) ≤ (1 : ℝ) *
      (H.grading (s + 0) z.1 + H.grading (s + 0) z.2)
    simpa only [Nat.add_zero, one_mul] using map_sub_le_add (H.grading s) z.1 z.2
  have hlin := smoothTameOn_continuousLinear L hL
  exact smoothTameOn_comp_topological hp ht
    (withSeminorms_pairGrading (withSeminorms_graded (fun i => H.level i) H.bond)
      (withSeminorms_graded (fun i => H.level i) H.bond))
    hU isOpen_univ (fun _ _ => mem_univ _) (smoothTameOn_prodMk hp ht hf hg) hlin

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.smoothTameOn_returnFlowCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.returnFlowCircle hS hT) :=
  hN.smoothTameOn_endpointFlowCircle hS hT C.right hN.right_radius_mem

theorem N01Properties.smoothTameOn_sectorReturnTransportCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.sectorReturnTransportCircle hS hT) := by
  let p := pairGrading (sectorGrading S) realGrading
  let q := (S.circle (3 / 4 : ℝ)).grading
  let U := sectorNeighborhood S base ε ε
  have hp : Monotone p := sectorPairGrading_monotone S
  have ht : WithSeminorms p := residual_sectorPair_withSeminorms S
  have hq : WithSeminorms q :=
    withSeminorms_graded (fun j => (S.circle (3 / 4 : ℝ)).level j) (S.circle (3 / 4 : ℝ)).bond
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hCircle := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) :=
    fun n => (hCircle.2.1 n).isComplete.completeSpace_coe
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hi : HasInterpolation q := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hflow : SmoothTameOn p q U (hN.returnFlowCircle hS hT) :=
    hN.smoothTameOn_returnFlowCircle hS hT
  have hchart : SmoothTameOn p q U (fun z : StateDirections S × ℝ => z.1.val.2.2.2) :=
    smoothTameOn_restrict_open (smoothTameOn_sectorChart S) hU (subset_univ _)
  have hdiff : SmoothTameOn p q U
      (fun z : StateDirections S × ℝ => z.1.val.2.2.2 - hN.returnFlowCircle hS hT z) :=
    smoothTameOn_circle_sub hp ht hU hchart hflow
  have hpair := smoothTameOn_prodMk hp ht hflow hdiff
  have hmap : MapsTo
      (fun z : StateDirections S × ℝ =>
        (hN.returnFlowCircle hS hT z, z.1.val.2.2.2 - hN.returnFlowCircle hS hT z)) U
      (circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) ×ˢ univ) :=
    fun z hz => ⟨hN.returnFlowCircle_positive hS hT z hz, mem_univ _⟩
  exact smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading hq hq) hU
    ((circlePositiveLiftDomain_isOpen hCircle hT hN.1.1 hγ).prod isOpen_univ) hmap hpair
    (smoothTameOn_circlePositiveInverseComposeLinear hCircle hT hN.1.1 hγ hi
      (fun m => -C.travel m))

theorem N01Properties.smoothTameOn_sectorReturnResidualCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.sectorReturnResidualCircle hS hT) := by
  let p := pairGrading (sectorGrading S) realGrading
  let q := (S.circle (3 / 4 : ℝ)).grading
  let U := sectorNeighborhood S base ε ε
  have hp : Monotone p := sectorPairGrading_monotone S
  have ht : WithSeminorms p := residual_sectorPair_withSeminorms S
  have hq : WithSeminorms q :=
    withSeminorms_graded (fun j => (S.circle (3 / 4 : ℝ)).level j) (S.circle (3 / 4 : ℝ)).bond
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hCircle := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) :=
    fun n => (hCircle.2.1 n).isComplete.completeSpace_coe
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hi : HasInterpolation q := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hu : SmoothTameOn p q U (hN.sectorReturnTransportCircle hS hT) :=
    hN.smoothTameOn_sectorReturnTransportCircle hS hT
  have hodd : SmoothTameOn p q U (fun z =>
      circleOddLinear hCircle (hN.sectorReturnTransportCircle hS hT z)) :=
    smoothTameOn_comp_topological hp ht hq hU isOpen_univ (fun _ _ => mem_univ _) hu
      (smoothTameOn_circleOddLinear hCircle)
  have heven : SmoothTameOn p q U (fun z =>
      circleEvenLinear hCircle (hN.sectorReturnTransportCircle hS hT z)) :=
    smoothTameOn_comp_topological hp ht hq hU isOpen_univ (fun _ _ => mem_univ _) hu
      (smoothTameOn_circleEvenLinear hCircle)
  have hpair := smoothTameOn_prodMk hp ht hodd heven
  have hmap : MapsTo
      (fun z : StateDirections S × ℝ =>
        (circleOddLinear hCircle (hN.sectorReturnTransportCircle hS hT z),
          circleEvenLinear hCircle (hN.sectorReturnTransportCircle hS hT z))) U
      (circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) ×ˢ univ) :=
    fun z hz => ⟨hN.sectorReturnTransportCircle_odd_positive hS hT z hz, mem_univ _⟩
  exact smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading hq hq) hU
    ((circlePositiveLiftDomain_isOpen hCircle hT hN.1.1 hγ).prod isOpen_univ) hmap hpair
    (smoothTameOn_circlePositiveInverseComposeLinear hCircle hT hN.1.1 hγ hi (fun _ => 0))

theorem N01Properties.smoothTameOn_returnResidualCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => hN.returnResidualCircle hS hT (liftSectorParameter S C z)) := by
  apply smoothTameOn_congr (hN.smoothTameOn_sectorReturnResidualCircle hS hT)
  intro z hz
  exact (hN.returnResidualCircle_lift hS hT z).symm

/-- All N02 clauses follow from the original physical and N01 hypotheses. -/
theorem N01Properties.exists_returnEquation
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ R : ReturnEquationData S, N02Properties D T S C R base ε := by
  obtain ⟨R, _, hR⟩ := hN.exists_returnEquation_of_smoothTame_residual hS hT
    (hN.returnResidualCircle hS hT) (hN.returnResidualCircle_decode hS hT)
    (hN.smoothTameOn_returnResidualCircle hS hT)
  exact ⟨R, hR⟩

end ContinuousFlexibility.Statements
