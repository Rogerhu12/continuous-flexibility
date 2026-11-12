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

private theorem n08_profileSum_bound {X Y B : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [NormedAddCommGroup B]
    (p : Seminorm ℝ X) (q : Seminorm ℝ Y)
    (f : X → Y) (nu : X → ℝ) (control : X → B)
    (scalarLift : ℝ → Y) (controlLift : B → Y)
    (heq : ∀ x, f x = scalarLift (nu x) + controlLift (control x))
    (hscalar : ∃ A : ℝ, 0 ≤ A ∧ ∀ a, q (scalarLift a) ≤ A * ‖a‖)
    (hcontrol : ∃ A : ℝ, 0 ≤ A ∧ ∀ u, q (controlLift u) ≤ A * ‖u‖)
    (K : ℝ) (hK : 0 ≤ K)
    (hnu : ∀ x, ‖nu x‖ ≤ p x) (hc : ∀ x, ‖control x‖ ≤ K * p x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, q (f x) ≤ A * p x := by
  obtain ⟨A1, hA1, hA1b⟩ := hscalar
  obtain ⟨A2, hA2, hA2b⟩ := hcontrol
  refine ⟨A1 + A2 * K, add_nonneg hA1 (mul_nonneg hA2 hK), fun x => ?_⟩
  rw [heq x]
  calc
    _ ≤ q (scalarLift (nu x)) + q (controlLift (control x)) := map_add_le_add q _ _
    _ ≤ A1 * ‖nu x‖ + A2 * ‖control x‖ := add_le_add (hA1b _) (hA2b _)
    _ ≤ A1 * p x + A2 * (K * p x) :=
      add_le_add (mul_le_mul_of_nonneg_left (hnu x) hA1)
        (mul_le_mul_of_nonneg_left (hc x) hA2)
    _ = _ := by ring

private theorem n08_tameLinear_of_zero_level_bound {X Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (L : X →ₗ[ℝ] Y)
    (hp : Monotone p)
    (h : ∀ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, q s (L x) ≤ K * p 0 x) :
    IsTameLinear p q L 0 0 := by
  intro s _
  obtain ⟨K, hK, hKb⟩ := h s
  refine ⟨⟨K, hK⟩, fun x => ?_⟩
  exact (hKb x).trans (mul_le_mul_of_nonneg_left (hp (Nat.zero_le _) x) hK)

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

private theorem n08ControlWeakCoordinate_bound (S : PhysicalSpacesData)
    (x : AnnularState S) :
    ‖n08ControlRestriction S x.2.2.1‖ ≤ n08ControlMeanConstant * stateGrading S 0 x :=
  (n08ControlRestriction_norm_le S x.2.2.1).trans
    (mul_le_mul_of_nonneg_left (n08ControlCoordinateCLM_bound S 0 x)
      n08ControlMeanConstant_nonneg)

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
        K * stateGrading S 0 x :=
  n08_profileSum_bound (X := AnnularState S) (Y := (S.height n08WeakControlWeight).Space)
    (B := ControlBanach) (stateGrading S 0) ((S.height n08WeakControlWeight).grading s)
    (n08LogProfileLift hT hS hN) (fun x : AnnularState S => x.2.1)
    (fun x : AnnularState S => n08ControlRestriction S x.2.2.1)
    (n08NuProfileLift hT hS hN) (n08WeakControlLift hT hS hN)
    (n08LogProfileLift_apply hT hS hN)
    (n08NuProfileLift_grading_bound hT hS hN s)
    (n08WeakControlLift_grading_bound hT hS hN s)
    n08ControlMeanConstant n08ControlMeanConstant_nonneg
    (n08NuCoordinateCLM_bound S 0) (n08ControlWeakCoordinate_bound S)

theorem n08LogProfileLift_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (stateGrading S) (S.height n08WeakControlWeight).grading
      (n08LogProfileLift hT hS hN).toLinearMap 0 0 :=
  n08_tameLinear_of_zero_level_bound
    (X := AnnularState S) (Y := (S.height n08WeakControlWeight).Space)
    (stateGrading S) (S.height n08WeakControlWeight).grading
    (n08LogProfileLift hT hS hN).toLinearMap (solve_stateGrading_monotone S)
    (n08LogProfileLift_grading_bound hT hS hN)

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
