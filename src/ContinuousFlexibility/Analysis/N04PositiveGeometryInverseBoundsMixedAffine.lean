import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedEnvelope
import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# The mixed inverse estimate on the original topological state space

The normed parameter space is only a finite affine slice. Both the
forward and inverse jets below are the original `SmoothDirections`
jets, evaluated on the images of the slice directions. The exact
identity and the true forward spatial differential provide the inverse
recurrence; no quantitative inverse premise is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E P V : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

def n04PositiveGeometry_fiberSliceLinear (L : P →L[ℝ] E) :
    (P × V) →L[ℝ] (E × V) :=
  (L.comp (ContinuousLinearMap.fst ℝ P V)).prod (ContinuousLinearMap.snd ℝ P V)

theorem n04PositiveGeometry_fiberSliceLinear_apply (L : P →L[ℝ] E) (q : P × V) :
    n04PositiveGeometry_fiberSliceLinear L q = (L q.1, q.2) := rfl

def n04PositiveGeometry_fiberSlice (a : E) (L : P →L[ℝ] E) (q : P × V) : E × V :=
  (a, 0) + n04PositiveGeometry_fiberSliceLinear L q

theorem n04PositiveGeometry_fiberSlice_apply (a : E) (L : P →L[ℝ] E) (q : P × V) :
    n04PositiveGeometry_fiberSlice a L q = (a + L q.1, q.2) := by
  simp only [n04PositiveGeometry_fiberSlice, n04PositiveGeometry_fiberSliceLinear_apply,
    Prod.mk_add_mk, zero_add]

theorem n04PositiveGeometry_fiberSlice_lift (a : E) (L : P →L[ℝ] E)
    (g : E × V → V) (q : P × V) :
    n04PositiveGeometry_fiberSlice a L
      (n04PositiveGeometry_fiberLift (fun p => g (n04PositiveGeometry_fiberSlice a L p)) q) =
        ((n04PositiveGeometry_fiberSlice a L q).1, g (n04PositiveGeometry_fiberSlice a L q)) := by
  simp only [n04PositiveGeometry_fiberSlice_apply, n04PositiveGeometry_fiberLift]

theorem n04PositiveGeometry_fiberSlice_contDiffAt
    {U : Set (E × V)} {f : E × V → V} (J : SmoothDirections U f)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U) :
    ContDiffAt ℝ ∞ (fun p => f (n04PositiveGeometry_fiberSlice a L p)) q := by
  have h := smoothDirections_contDiffOn_finiteAffine J (a, (0 : V))
    (n04PositiveGeometry_fiberSliceLinear L)
  have ho : IsOpen ((fun p => (a, (0 : V)) + n04PositiveGeometry_fiberSliceLinear L p) ⁻¹' U) :=
    J.open_domain.preimage (continuous_const.add
      (n04PositiveGeometry_fiberSliceLinear L).continuous)
  exact h.contDiffAt (ho.mem_nhds hq)

theorem n04PositiveGeometry_fiberSlice_iteratedFDeriv
    {U : Set (E × V)} {f : E × V → V} (J : SmoothDirections U f)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U)
    (n : ℕ) (v : Fin n → P × V) :
    iteratedFDeriv ℝ n (fun p => f (n04PositiveGeometry_fiberSlice a L p)) q v =
      J.D n (n04PositiveGeometry_fiberSlice a L q)
        (fun i => n04PositiveGeometry_fiberSliceLinear L (v i)) :=
  smoothDirections_iteratedFDeriv_finiteAffine J (a, (0 : V))
    (n04PositiveGeometry_fiberSliceLinear L) n hq v

theorem n04PositiveGeometry_fiberSlice_projectedJet
    {U : Set (E × V)} {f : E × V → V} (J : SmoothDirections U f)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U)
    {n : ℕ} (b : Fin n → Bool) (v : Fin n → P × V) :
    n04PositiveGeometry_projectedJet b (fun p => f (n04PositiveGeometry_fiberSlice a L p)) q v =
      J.D n (n04PositiveGeometry_fiberSlice a L q)
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (b i) (v i))) := by
  rw [n04PositiveGeometry_projectedJet_apply]
  exact n04PositiveGeometry_fiberSlice_iteratedFDeriv J a L hq n _

private theorem fiberSlice_inverse_germ
    {U : Set (E × V)} {f g : E × V → V} (hU : IsOpen U)
    (hfg : ∀ p ∈ U, f (p.1, g p) = p.2)
    (a : E) (L : P →L[ℝ] E) {q : P × V}
    (hq : n04PositiveGeometry_fiberSlice a L q ∈ U) :
    n04PositiveGeometry_fiberLift (fun p => f (n04PositiveGeometry_fiberSlice a L p)) ∘
      n04PositiveGeometry_fiberLift (fun p => g (n04PositiveGeometry_fiberSlice a L p))
        =ᶠ[𝓝 q] id := by
  have ho : IsOpen (n04PositiveGeometry_fiberSlice a L ⁻¹' U) :=
    hU.preimage (continuous_const.add (n04PositiveGeometry_fiberSliceLinear L).continuous)
  filter_upwards [ho.mem_nhds hq] with p hp
  apply Prod.ext
  · rfl
  · change f (n04PositiveGeometry_fiberSlice a L
        (n04PositiveGeometry_fiberLift (fun p => g (n04PositiveGeometry_fiberSlice a L p)) p)) = p.2
    rw [n04PositiveGeometry_fiberSlice_lift]
    exact hfg _ hp

/-- An actual original-state inverse estimate on any finite affine
slice. The forward premise only bounds the requested state prefix.
The scale exponent and height factor are retained exactly. -/
theorem n04PositiveGeometry_mixedInverse_affine_bound
    (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧ ∃ d : ℕ,
    ∀ (U W : Set (E × V)) (f g : E × V → V)
      (JF : SmoothDirections W f) (JG : SmoothDirections U g)
      (a : E) (L : P →L[ℝ] E) (q : P × V),
      n04PositiveGeometry_fiberSlice a L q ∈ U →
      ((n04PositiveGeometry_fiberSlice a L q).1, g (n04PositiveGeometry_fiberSlice a L q)) ∈ W →
      (∀ p ∈ U, f (p.1, g p) = p.2) →
      ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
      ∀ (K C : ℕ), 1 ≤ C → ∀ (B : V →L[ℝ] V),
      (∀ v : V, B (JF.D 1
        ((n04PositiveGeometry_fiberSlice a L q).1, g (n04PositiveGeometry_fiberSlice a L q))
        (fun _ => (0, v))) = v) → ‖B‖ ≤ M →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → P × V,
        ‖JF.D j ((n04PositiveGeometry_fiberSlice a L q).1,
            g (n04PositiveGeometry_fiberSlice a L q))
          (fun i => n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (w.isState i) (v i)))‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1) * ∏ i, ‖v i‖) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K → ∀ v : Fin n → P × V,
        ‖JG.D n (n04PositiveGeometry_fiberSlice a L q)
          (fun i => n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (w.isState i) (v i)))‖ ≤
          A * M ^ d * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1) * ∏ i, ‖v i‖ := by
  let h := n04PositiveGeometry_mixedInverse_polynomial_envelope P V n
  let A : ℝ := h.choose
  let d : ℕ := h.choose_spec.2.choose
  have hA : 1 ≤ A := h.choose_spec.1
  have hbound : N04PositiveGeometryMixedInverseEnvelope P V n A d := h.choose_spec.2.choose_spec
  refine ⟨A, hA, d, ?_⟩
  intro U W f g JF JG a L q hq hfq hfg M H t hM hH hHM ht K C hC B hB hBM hforward hn w hw v
  let F : P × V → V := fun p => f (n04PositiveGeometry_fiberSlice a L p)
  let G : P × V → V := fun p => g (n04PositiveGeometry_fiberSlice a L p)
  have hfq' : n04PositiveGeometry_fiberSlice a L (n04PositiveGeometry_fiberLift G q) ∈ W := by
    rw [n04PositiveGeometry_fiberSlice_lift]
    exact hfq
  have hF : ContDiffAt ℝ ∞ F (n04PositiveGeometry_fiberLift G q) :=
    n04PositiveGeometry_fiberSlice_contDiffAt JF a L hfq'
  have hG : ContDiffAt ℝ ∞ G q := n04PositiveGeometry_fiberSlice_contDiffAt JG a L hq
  have hFG : n04PositiveGeometry_fiberLift F ∘ n04PositiveGeometry_fiberLift G =ᶠ[𝓝 q] id :=
    fiberSlice_inverse_germ JG.open_domain hfg a L hq
  have hB' : B.comp ((fderiv ℝ F (n04PositiveGeometry_fiberLift G q)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro v
    have hj := n04PositiveGeometry_fiberSlice_iteratedFDeriv JF a L hfq' 1
      (fun _ => ((0 : P), v))
    simp only [iteratedFDeriv_one_apply, n04PositiveGeometry_fiberSliceLinear_apply,
      map_zero, n04PositiveGeometry_fiberSlice_lift] at hj
    change B (fderiv ℝ F (n04PositiveGeometry_fiberLift G q) (0, v)) = v
    exact (congrArg B hj).trans (hB v)
  have hforward' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K) :
      ‖n04PositiveGeometry_projectedJet u.isState F (n04PositiveGeometry_fiberLift G q)‖ ≤
        M * parameterHeightWeight H u.stateArity * t ^ (u.angleArity + C * u.stateArity - 1) := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro v
    rw [n04PositiveGeometry_fiberSlice_projectedJet JF a L hfq',
      n04PositiveGeometry_fiberSlice_lift]
    exact hforward j hj hjn u hu v
  have hi := hbound hn M H t hM hH hHM ht K C hC F G q hF hG hFG B hB' hBM hforward' w hw
  calc
    _ = ‖n04PositiveGeometry_projectedJet w.isState G q v‖ :=
      congrArg norm (n04PositiveGeometry_fiberSlice_projectedJet JG a L hq w.isState v).symm
    _ ≤ ‖n04PositiveGeometry_projectedJet w.isState G q‖ * ∏ i, ‖v i‖ :=
      (n04PositiveGeometry_projectedJet w.isState G q).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right hi (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

end ContinuousFlexibility.Analysis
