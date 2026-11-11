import ContinuousFlexibility.Analysis.N08NuProfileLift
import ContinuousFlexibility.Analysis.N08WeakControlLift
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# The actual logarithmic state profile in a positive weighted space

The scalar direction and the normalized weak control series have now both
been realized in the same physical model. Their sum is a continuous linear
map whose every output order is controlled by the level-zero state norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_profileCoordinates_bound {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (s : ℕ) (x : E × ℝ × F × F) :
    ‖x.2.1‖ ≤ pairGrading p (pairGrading realGrading (pairGrading q q)) s x ∧
      q s x.2.2.1 ≤ pairGrading p (pairGrading realGrading (pairGrading q q)) s x := by
  change ‖x.2.1‖ ≤ p s x.1 + (‖x.2.1‖ + (q s x.2.2.1 + q s x.2.2.2)) ∧
    q s x.2.2.1 ≤ p s x.1 + (‖x.2.1‖ + (q s x.2.2.1 + q s x.2.2.2))
  have hp := apply_nonneg (p s) x.1
  have hq := apply_nonneg (q s) x.2.2.1
  have hr := apply_nonneg (q s) x.2.2.2
  have ha := norm_nonneg x.2.1
  constructor <;> linarith

def n08NuCoordinateCLM (S : PhysicalSpacesData) : AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (CircleSpace S × CircleSpace S)).comp
    (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

def n08ControlCoordinateCLM (S : PhysicalSpacesData) :
    AnnularState S →L[ℝ] CircleSpace S :=
  (ContinuousLinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
    ((ContinuousLinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
      (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))))

theorem n08NuCoordinateCLM_apply (S : PhysicalSpacesData) (x : AnnularState S) :
    n08NuCoordinateCLM S x = x.2.1 := rfl

theorem n08ControlCoordinateCLM_apply (S : PhysicalSpacesData) (x : AnnularState S) :
    n08ControlCoordinateCLM S x = x.2.2.1 := rfl

theorem n08NuCoordinateCLM_bound (S : PhysicalSpacesData) (s : ℕ) (x : AnnularState S) :
    ‖n08NuCoordinateCLM S x‖ ≤ stateGrading S s x :=
  (n08_profileCoordinates_bound (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading s x).1

theorem n08ControlCoordinateCLM_bound (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading s (n08ControlCoordinateCLM S x) ≤ stateGrading S s x :=
  (n08_profileCoordinates_bound (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading s x).2

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08LogProfileLift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    AnnularState S →L[ℝ] (S.height n08WeakControlWeight).Space :=
  (n08NuProfileLift hT hS hN).comp (n08NuCoordinateCLM S) +
    (n08WeakControlLift hT hS hN).comp
      ((n08ControlRestriction S).comp (n08ControlCoordinateCLM S))

theorem n08LogProfileLift_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    n08LogProfileLift hT hS hN x = n08NuProfileLift hT hS hN x.2.1 +
      n08WeakControlLift hT hS hN (n08ControlRestriction S x.2.2.1) := rfl

theorem n08LogProfileLift_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode (n08LogProfileLift hT hS hN x) p =
      n08_stateLogProfile D S C x p.1 := by
  rw [n08LogProfileLift_apply hT hS hN x, map_add, Pi.add_apply,
    n08NuProfileLift_decode hT hS hN, n08WeakControlLift_restriction_decode hT hS hN]
  rfl

theorem n08LogProfileLift_grading_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : AnnularState S,
      (S.height n08WeakControlWeight).grading s (n08LogProfileLift hT hS hN x) ≤
        K * stateGrading S 0 x := by
  obtain ⟨A, hA, hAb⟩ := n08NuProfileLift_grading_bound hT hS hN s
  obtain ⟨B, hB, hBb⟩ := n08WeakControlLift_grading_bound hT hS hN s
  refine ⟨A + B * n08ControlMeanConstant,
    add_nonneg hA (mul_nonneg hB n08ControlMeanConstant_nonneg), fun x => ?_⟩
  have hn : ‖x.2.1‖ ≤ stateGrading S 0 x := n08NuCoordinateCLM_bound S 0 x
  have hc : ‖n08ControlRestriction S x.2.2.1‖ ≤
      n08ControlMeanConstant * stateGrading S 0 x :=
    (n08ControlRestriction_norm_le S x.2.2.1).trans
      (mul_le_mul_of_nonneg_left (n08ControlCoordinateCLM_bound S 0 x)
        n08ControlMeanConstant_nonneg)
  rw [n08LogProfileLift_apply hT hS hN x]
  calc
    _ ≤ (S.height n08WeakControlWeight).grading s (n08NuProfileLift hT hS hN x.2.1) +
        (S.height n08WeakControlWeight).grading s
          (n08WeakControlLift hT hS hN (n08ControlRestriction S x.2.2.1)) :=
      map_add_le_add _ _ _
    _ ≤ A * ‖x.2.1‖ + B * ‖n08ControlRestriction S x.2.2.1‖ := add_le_add (hAb _) (hBb _)
    _ ≤ A * stateGrading S 0 x + B * (n08ControlMeanConstant * stateGrading S 0 x) :=
      add_le_add (mul_le_mul_of_nonneg_left hn hA) (mul_le_mul_of_nonneg_left hc hB)
    _ = _ := by ring

theorem n08LogProfileLift_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (stateGrading S) (S.height n08WeakControlWeight).grading
      (n08LogProfileLift hT hS hN).toLinearMap 0 0 := by
  intro s _
  obtain ⟨K, hK, hKb⟩ := n08LogProfileLift_grading_bound hT hS hN s
  refine ⟨⟨K, hK⟩, fun x => (hKb x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (solve_stateGrading_monotone S (Nat.zero_le _) x) hK

theorem n08LogProfileLift_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    n08LogProfileLift hT hS hN C.referenceState = 0 := by
  apply (hS.1 n08WeakControlWeight).2.2.2.2.2.1
  funext p
  rw [n08LogProfileLift_decode hT hS hN C.referenceState p]
  change n08_stateLogProfile D S C C.referenceState p.1 =
    (S.height n08WeakControlWeight).decode 0 p
  simp only [n08_stateLogProfile, hN.2.2.1.2.2.1, stateControlSum,
    n08_stateKappa_reference hN.2.2.1, zero_mul, tsum_zero, zero_add,
    map_zero, Pi.zero_apply]

theorem n08LogProfileLift_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x0 : AnnularState S) :
    UniformTameGerm (stateGrading S) (S.height n08WeakControlWeight).grading
      x0 (n08LogProfileLift hT hS hN) :=
  uniformTameGerm_continuousLinear (solve_stateGrading_withSeminorms S) x0
    (n08LogProfileLift hT hS hN) (n08LogProfileLift_isTame hT hS hN)

end ContinuousFlexibility.Statements
