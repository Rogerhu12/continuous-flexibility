module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsKernelTrace

/-!
# Actual physical root coefficient traces with polynomial material cost

The finite spatial kernel sum is the actual radial trace, including its
intrinsic angular derivatives. Summing its genuine parameter jets gives
one common low base, a fixed spatial loss, and the original positive
parameter height factor for the physical drift and speed ratio.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_angularFiniteSum_parameter_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {ι : Type*} [Fintype ι] {U : Set E} {f : ι → E × ℝ → ℝ} {g : E × ℝ → ℝ}
    (Ji : ∀ i, SmoothDirections (U ×ˢ (univ : Set ℝ)) (f i))
    (hU : IsOpen U) (heq : EqOn (fun y => ∑ i, f i y) g (U ×ˢ univ))
    (k b : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (v : Fin k → E)
    (J : SmoothDirections U (fun y => iteratedDeriv b (fun η => g (y, η)) θ))
    (M : ι → ℝ)
    (hb : ∀ i, ‖(smoothDirections_angularStateSlice (Ji i) b θ).D k x v‖ ≤ M i) :
    ‖J.D k x v‖ ≤ ∑ i, M i := by
  let JS := smoothDirections_finiteSum (hU.prod isOpen_univ) Ji
  let Q := JS.congr (fun y hy => heq hy)
  let w := StateAngleWord.stateThenAngle k b
  have hs : ∀ z : Fin w.stateArity → E,
      (smoothDirections_angularStateSlice Q w.angleArity θ).D w.stateArity x z =
        ∑ i, (smoothDirections_angularStateSlice (Ji i) w.angleArity θ).D w.stateArity x z := by
    intro z
    rw [← smoothDirections_joint_pureSlots Q
      (fun a η => smoothDirections_angularStateSlice Q a η) w hx θ z]
    change (smoothDirections_finiteSum (hU.prod isOpen_univ) Ji).D
      (b + k) (x, θ) (w.pureSlots z) = _
    rw [smoothDirections_finiteSum_D_apply]
    exact Finset.sum_congr rfl (fun i _ => smoothDirections_joint_pureSlots
      (Ji i) (fun a η => smoothDirections_angularStateSlice (Ji i) a η) w hx θ z)
  have hwk : w.stateArity = k := StateAngleWord.stateThenAngle_stateArity k b
  have hwb : w.angleArity = b := StateAngleWord.stateThenAngle_angleArity k b
  rw [hwk, hwb] at hs
  have he : J.D k x v = ∑ i, (smoothDirections_angularStateSlice (Ji i) b θ).D k x v :=
    (congrArg (fun A : E [×k]→L[ℝ] ℝ => A v)
      (J.unique (smoothDirections_angularStateSlice Q b θ) k x hx)).trans (hs v)
  rw [he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hb i))

local instance n04PositivePhysicalPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The finite radial and intrinsic angular prefix of the original
physical root drift and speed ratio has a genuine normalized bound.
Only the additional angular order appears in the power of R. -/
theorem n04PositiveGeometry_physicalRootTrace_finiteShift_power
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ r ∈ radialCore D, deriv D.w r = 0 →
      ∀ a d : ℕ, a + d ≤ N →
      ∀ π : PolarPoint →L[ℝ] ℝ, ‖π‖ ≤ 1 → ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => iteratedDeriv (b + d) (radialBoundaryJet
          (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C z) p)) r a) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections S × ℝ),
      (∀ j, pairGrading (sectorGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading S) realGrading (s + inputLoss) z ≤ R →
      (∀ j, pairGrading (sectorGrading S) realGrading (s + inputLoss) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let data := n04PositiveGeometry_rootKernelTerm_finite_power
    hT hS hN hε hE N requestedBase
  let B := data.choose
  let inputLoss := data.choose_spec.choose
  have hB := data.choose_spec.choose_spec.1
  have hterms := data.choose_spec.choose_spec.2
  let count : ℝ := 1 + ∑ j : Fin (N + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hcount : 1 ≤ count := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hcard (n : ℕ) (hn : n ≤ N) :
      (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count := by
    let j : Fin (N + 1) := ⟨n, by omega⟩
    exact (Finset.single_le_sum
      (f := fun i : Fin (N + 1) => (Fintype.card (OrderedFinpartition i.val) : ℝ))
      (fun i _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition i.val)))
      (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1))
  refine ⟨B, inputLoss, hB, fun K s => ?_⟩
  let orderData := hterms K s
  let C0 := orderData.choose
  let A := orderData.choose_spec.choose
  have hC0 := orderData.choose_spec.choose_spec.1
  have hA := orderData.choose_spec.choose_spec.2.1
  have hb := orderData.choose_spec.choose_spec.2.2
  refine ⟨count * C0, A, one_le_mul_of_one_le_of_one_le hcount hC0, hA, ?_⟩
  intro r hr hroot a d had π hπ b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let Ji := fun c : OrderedFinpartition (a + d) =>
    n04PositiveGeometry_rootKernelTerm_joint hT hS hN hε hr hroot
      c (cylinderMixedWord a d) π
  let g : ((StateDirections S × ℝ) × ℝ) → ℝ := fun y => iteratedDeriv d
    (radialBoundaryJet (fun p => π
      (n06PhysicalRootFields D S C (liftSectorParameter S C y.1) p)) r a) y.2
  have heq : EqOn (fun y => ∑ c : OrderedFinpartition (a + d), π
      (n04PositiveGeometry_rootRadialKernel c.length
        (n04PositiveGeometry_rootSpatialInput (D := D) (C := C)
          c (cylinderMixedWord a d) r y))) g
        (sectorNeighborhood S base ε ε ×ˢ univ) := by
    intro y hy
    exact (n04PositiveGeometry_physicalRootTrace_kernel_formula
      hT hS hN hr hroot y.1 hy.1 π a d y.2).symm
  let Jg : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => iteratedDeriv b (fun η => g (y, η)) θ) :=
    J.congr (fun y _ => (congrFun (circle_iteratedDeriv_iteratedDeriv
      (radialBoundaryJet (fun p => π
        (n06PhysicalRootFields D S C (liftSectorParameter S C y) p)) r a) b d) θ).symm)
  let M := C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
    R ^ ((b : ℝ) / ((s : ℝ) + 1))
  have hsum := n04PositiveGeometry_angularFiniteSum_parameter_bound Ji
    (sectorNeighborhood_isOpen S base ε ε) heq k b z hz θ v Jg (fun _ => M)
      (fun c => hb r hr hroot (a + d) had c (cylinderMixedWord a d) π hπ b hbs θ
        (smoothDirections_angularStateSlice (Ji c) b θ) k hk z hz hzlow v hv R hR hzR hvR)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
      (Real.rpow_nonneg (zero_le_one.trans (hE r hr)) _))
      (parameterHeightWeight_nonneg (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) k))
    (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hc := mul_le_mul_of_nonneg_right (hcard (a + d) had) hM
  have hsum' : ‖J.D k z v‖ ≤ (Fintype.card (OrderedFinpartition (a + d)) : ℝ) * M := by
    simpa only [Jg, SmoothDirections.congr, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hsum
  exact hsum'.trans (hc.trans_eq (by dsimp only [M]; ring))

end ContinuousFlexibility.Analysis
