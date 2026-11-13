import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledMovingComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedAffine

/-!
# Moving-point estimates for the original state towers

Only the affine slice is finite dimensional. The conclusion evaluates
the supplied genuine tower on the original topological state space.
The selected state singletons keep the outer state prefix unchanged,
even when the requested spatial order grows.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E P V Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

theorem n04PositiveGeometry_fiberSlice_contDiffAt_output
    {U : Set (E × V)} {f : E × V → Z} (J : SmoothDirections U f)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U) :
    ContDiffAt ℝ ∞ (fun p => f (n04PositiveGeometry_fiberSlice a L p)) q := by
  have h := smoothDirections_contDiffOn_finiteAffine J (a, (0 : V))
    (n04PositiveGeometry_fiberSliceLinear L)
  have ho : IsOpen ((fun p => (a, (0 : V)) + n04PositiveGeometry_fiberSliceLinear L p) ⁻¹' U) :=
    J.open_domain.preimage (continuous_const.add
      (n04PositiveGeometry_fiberSliceLinear L).continuous)
  exact h.contDiffAt (ho.mem_nhds hq)

theorem n04PositiveGeometry_fiberSlice_projectedJet_output
    {U : Set (E × V)} {f : E × V → Z} (J : SmoothDirections U f)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U)
    {n : ℕ} (b : Fin n → Bool) (v : Fin n → P × V) :
    n04PositiveGeometry_projectedJet b (fun p => f (n04PositiveGeometry_fiberSlice a L p)) q v =
      J.D n (n04PositiveGeometry_fiberSlice a L q)
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (b i) (v i))) := by
  rw [n04PositiveGeometry_projectedJet_apply]
  exact smoothDirections_iteratedFDeriv_finiteAffine J (a, (0 : V))
    (n04PositiveGeometry_fiberSliceLinear L) n hq _

/-- A field with weighted order `u + C κ`, evaluated at an actual
moving point with weighted order `u + C κ - 1`, retains its weighted
order. All towers and direction vectors belong to the original state
space. The finite slice is an auxiliary calculus argument only. -/
theorem n04PositiveGeometry_movingPoint_affine_bound
    (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (U W : Set (E × V)) (f : E × V → Z) (g : E × V → V)
      (JF : SmoothDirections W f) (JG : SmoothDirections U g)
      (JO : SmoothDirections U (fun p => f (p.1, g p)))
      (a : E) (L : P →L[ℝ] E) (q : P × V),
      n04PositiveGeometry_fiberSlice a L q ∈ U →
      ((n04PositiveGeometry_fiberSlice a L q).1, g (n04PositiveGeometry_fiberSlice a L q)) ∈ W →
      ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
      ∀ (K C : ℕ), 1 ≤ C →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → P × V,
        ‖JF.D j ((n04PositiveGeometry_fiberSlice a L q).1,
            g (n04PositiveGeometry_fiberSlice a L q))
          (fun i => n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (w.isState i) (v i)))‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity) * ∏ i, ‖v i‖) →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → P × V,
        ‖JG.D j (n04PositiveGeometry_fiberSlice a L q)
          (fun i => n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (w.isState i) (v i)))‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1) * ∏ i, ‖v i‖) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K → ∀ v : Fin n → P × V,
        ‖JO.D n (n04PositiveGeometry_fiberSlice a L q)
          (fun i => n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (w.isState i) (v i)))‖ ≤
          A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity) * ∏ i, ‖v i‖ := by
  obtain ⟨A, hA, hbound⟩ :=
    n04PositiveGeometry_movingPoint_polynomial_envelope (P := P) (V := V) (Z := Z) n
  refine ⟨A, hA, ?_⟩
  intro U W f g JF JG JO a L q hq hfq M H t hM hH hHM ht K C hC houter hinner hn w hw v
  let F : P × V → Z := fun p => f (n04PositiveGeometry_fiberSlice a L p)
  let G : P × V → V := fun p => g (n04PositiveGeometry_fiberSlice a L p)
  have hfq' : n04PositiveGeometry_fiberSlice a L (n04PositiveGeometry_fiberLift G q) ∈ W := by
    rw [n04PositiveGeometry_fiberSlice_lift]
    exact hfq
  have hF : ContDiffAt ℝ ∞ F (n04PositiveGeometry_fiberLift G q) :=
    n04PositiveGeometry_fiberSlice_contDiffAt_output JF a L hfq'
  have hG : ContDiffAt ℝ ∞ G q := n04PositiveGeometry_fiberSlice_contDiffAt JG a L hq
  have houter' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K) :
      ‖n04PositiveGeometry_projectedJet u.isState F (n04PositiveGeometry_fiberLift G q)‖ ≤
        M * parameterHeightWeight H u.stateArity * t ^ (u.angleArity + C * u.stateArity) := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro v
    rw [n04PositiveGeometry_fiberSlice_projectedJet_output JF a L hfq',
      n04PositiveGeometry_fiberSlice_lift]
    exact houter j hj hjn u hu v
  have hinner' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K) :
      ‖n04PositiveGeometry_projectedJet u.isState G q‖ ≤
        M * parameterHeightWeight H u.stateArity * t ^ (u.angleArity + C * u.stateArity - 1) := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro v
    rw [n04PositiveGeometry_fiberSlice_projectedJet JG a L hq]
    exact hinner j hj hjn u hu v
  have hi := hbound M H t hM hH hHM ht K C hC F G q hF hG houter' hinner' hn w hw
  have hcomp : F ∘ n04PositiveGeometry_fiberLift G =
      (fun p => f ((n04PositiveGeometry_fiberSlice a L p).1,
        g (n04PositiveGeometry_fiberSlice a L p))) := by
    funext p
    exact congrArg f (n04PositiveGeometry_fiberSlice_lift a L g p)
  have he : n04PositiveGeometry_projectedJet w.isState
      (F ∘ n04PositiveGeometry_fiberLift G) q v =
      JO.D n (n04PositiveGeometry_fiberSlice a L q)
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (w.isState i) (v i))) := by
    rw [hcomp]
    exact n04PositiveGeometry_fiberSlice_projectedJet_output JO a L hq w.isState v
  calc
    _ = ‖n04PositiveGeometry_projectedJet w.isState (F ∘ n04PositiveGeometry_fiberLift G) q v‖ :=
      congrArg norm he.symm
    _ ≤ ‖n04PositiveGeometry_projectedJet w.isState (F ∘ n04PositiveGeometry_fiberLift G) q‖ *
        ∏ i, ‖v i‖ :=
      (n04PositiveGeometry_projectedJet w.isState (F ∘ n04PositiveGeometry_fiberLift G) q).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right hi (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

end ContinuousFlexibility.Analysis
