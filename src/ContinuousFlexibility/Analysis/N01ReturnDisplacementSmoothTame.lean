import ContinuousFlexibility.Analysis.N01ReturnDisplacementCircle
import ContinuousFlexibility.Analysis.CircleAverageCompositionSmoothTame
import ContinuousFlexibility.Analysis.CircleProductSmoothTame
import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# Full smooth tameness of the actual independent-residual displacement

The compact derivative average, its product with the independent
residual, and its composition with the actual return chart all use
their genuine circle-space towers. This proves the original divided
difference displacement jointly smooth tame in the state and the
independent residual. Decoding also gives the true joint angle tower.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem solve_smoothTameOn_fst
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F) {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : E → G} (hf : SmoothTameOn p r U f) :
    SmoothTameOn (pairGrading p q) r (U ×ˢ univ) (fun x : E × F => f x.1) := by
  let L : E × F →L[ℝ] E := ContinuousLinearMap.fst ℝ E F
  have hb (n : ℕ) (x : E × F) : p n (L x) ≤ (1 : ℝ) * pairGrading p q n x := by
    change p n x.1 ≤ 1 * (p n x.1 + q n x.2)
    simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (q n) x.2)
  have h := solve_smoothTameOn_precomp hf L (le_refl (1 : ℝ)) hb
  have heq : L ⁻¹' U = U ×ˢ (univ : Set F) := by
    ext x
    change x.1 ∈ U ↔ x.1 ∈ U ∧ x.2 ∈ (univ : Set F)
    simp only [mem_univ, and_true]
  rw [heq] at h
  exact h

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

theorem smoothTameOn_circleDerivativeLinear
    {T : MaterialData} {γ : ℝ} {H : CircleModelData} (hH : IsCircleModel T γ H) :
    SmoothTameOn H.grading H.grading univ (circleDerivativeLinear hH) := by
  exact smoothTameOn_congr
    (smoothTameOn_continuousLinear (circleDerivativeContinuousLinear hH)
      (circleDerivativeLinear_isTame hH))
    (fun u _ => circleDerivativeContinuousLinear_apply hH u)

theorem smoothTameOn_circleProduct_maps
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (ht : WithSeminorms p)
    {U : Set E} (hU : IsOpen U) {f g : E → H.Space}
    (hf : SmoothTameOn p H.grading U f) (hg : SmoothTameOn p H.grading U g) :
    SmoothTameOn p H.grading U (fun x => circleProductBilinear hH hT hD hγ (f x) (g x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  exact smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading htop htop)
    hU isOpen_univ (fun _ _ => mem_univ _) (smoothTameOn_prodMk hp ht hf hg)
    (smoothTameOn_circleProduct hH hT hD hγ hi)

local instance n01ReturnDisplacementSmoothTameStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.smoothTameOn_returnCorrectionDslopeCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.returnCorrectionDslopeCircle hS hT) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp := sectorPairGrading_monotone S
  have ht := sectorPairGrading_withSeminorms S
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hder : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => circleDerivativeLinear hH (hN.returnTransportInverseCircle hS hT z)) :=
    smoothTameOn_comp_topological hp ht htop hU isOpen_univ (fun _ _ => mem_univ _)
      (hN.smoothTameOn_returnTransportInverseCircle hS hT)
      (smoothTameOn_circleDerivativeLinear hH)
  exact smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading htop htop)
    hU isOpen_univ (fun _ _ => mem_univ _)
    (smoothTameOn_prodMk hp ht (hN.smoothTameOn_sectorReturnResidualCircle hS hT) hder)
    (smoothTameOn_circleAverageComposeLinear hH hT hN.1.1 (by norm_num)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0))

theorem N01Properties.smoothTameOn_returnCorrectionDisplacementCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        hN.returnCorrectionDisplacementCircleLinear hS hT x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  let q := pairGrading p H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp : Monotone q := tamePairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => H.level n) H.bond)
  have ht : WithSeminorms q := withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hρ : SmoothTameOn q H.grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × H.Space => x.2) :=
    smoothTameOn_restrict_open
      (smoothTameOn_continuousLinear (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) H.Space)
        (inverseTame_snd p H.grading)) hU (subset_univ _)
  have hds := solve_smoothTameOn_fst H.grading (hN.smoothTameOn_returnCorrectionDslopeCircle hS hT)
  have hprod := smoothTameOn_circleProduct_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp ht hU hds hρ
  have hamp := smoothTameOn_add hp hρ hprod
  have hchart := solve_smoothTameOn_fst H.grading (hN.smoothTameOn_rightReturnChartCircle hS hT)
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun m => -C.travel m) hp ht hU hchart hamp
  apply smoothTameOn_congr hcomp
  intro x hx
  simp only [N01Properties.returnCorrectionDisplacementCircleLinear, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply]

def N01Properties.returnCorrectionDisplacement_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun p : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        returnCorrectionDisplacementLinear S C (liftSectorParameter S C p.1.1) m p.2 p.1.2) := by
  let J := (hN.smoothTameOn_returnCorrectionDisplacementCircleLinear hS hT).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  apply (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).congrOn
  intro p hp
  exact hN.returnCorrectionDisplacementCircleLinear_decode hS hT p.1.1 hp.1.1 p.1.2 m p.2

end ContinuousFlexibility.Statements
