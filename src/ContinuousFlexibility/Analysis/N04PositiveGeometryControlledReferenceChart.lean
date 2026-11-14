module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamilyMaterial
public import ContinuousFlexibility.Analysis.N04PositiveGeometryReferencePullbackCosts
public import ContinuousFlexibility.Analysis.N04PositiveGeometrySlotKernelBounds
public import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
public import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# The radial chart in the actual fixed reference gauge

The chart is the same chosen inverse transport followed by the fixed
reference coordinate. Its exact partition formula keeps both the
original parameter height factor and the saved pure spatial order.
Only the material certificate of that reference family is consumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- A fixed radial scalar pullback does not enlarge ordinary jets. -/
theorem n04PositiveGeometry_norm_radial_pullback_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (q : PolarPoint) :
    ‖iteratedFDeriv ℝ j (fun p : PolarPoint => f p.1) q‖ ≤
      ‖iteratedFDeriv ℝ j f q.1‖ := by
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hb := norm_iteratedFDeriv_comp_linear_le_at L (hf.contDiffAt (x := L q)) j
  have hp : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg L)
    (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  exact hb.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _))

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- Every positive joint word of the literal radial chart inherits the
actual inverse-transport budget. The envelope is chosen before the
component, state, point, word, or offset. No bound on an angular lift
value is used. -/
theorem n04PositiveGeometry_controlledReferenceChart_radial_saved_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    (N : ℕ) (A RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ (U : Set V), ∀ state : V → AnnularState W.S × ℝ,
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ JS : SmoothDirections (U ×ˢ univ) (fun z =>
      G.toN04PositiveGeometryControlData.σ (state z.1) i z.2),
    ∀ J : SmoothDirections (U ×ˢ univ) (fun z =>
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (Y i))
        (G.toN04PositiveGeometryControlData.σ (state z.1) i) z.2).1),
    ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, ∀ offset : ℕ,
    ∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε →
      stateSector W.S (state x).1 →
    ∀ p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ),
    ∀ v : Fin n → (V × PolarPoint), ∀ H t : ℝ,
      0 ≤ H → H ≤ RH → 1 ≤ t →
    (∀ c : OrderedFinpartition n, ∀ j : Fin c.length,
      ‖JS.D (c.partSize j) (x, p) (v ∘ c.emb j)‖ ≤
        A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
          parameterHeightWeight H (w.restrict (c.emb j)).stateArity *
            t ^ n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb j)) offset) →
      |J.D n (x, p) v| ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B * parameterHeightWeight H w.stateArity *
          t ^ n04PositiveGeometry_savedSpatialCost w offset := by
  classical
  obtain ⟨Br, hBr, hrefjets⟩ :=
    n04PositiveGeometry_reference_prefix_material_cost W.floor hmaterial N
  let D : ℝ := max 1 (max A Br)
  have hD : 1 ≤ D := le_max_left _ _
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hBrD : Br ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  let L : ℝ := max 1 RH
  have hL : 1 ≤ L := le_max_left _ _
  let P : ℝ := 1 + ∑ j : Fin (N + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hP : 1 ≤ P := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
  have hcard (n : ℕ) (hn : n ≤ N) : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ P :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition j.val)))
      (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (N + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨B₀, _, hpack⟩ :=
    n04PositiveGeometry_polynomial_sample_pack (P * L ^ N) D (N + 1)
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro U state i JS J n hn hnN w offset x hx hz hs p hp v H t hH hHR ht hraw
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let M : ℝ := D * E ^ D
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow hE (zero_le_one.trans hD))
  have hraise {a : ℝ} (ha : a ≤ D) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hD)
  let f : V × PolarPoint → PolarPoint := fun z =>
    G.toN04PositiveGeometryControlData.σ (state z.1) i z.2
  let g : PolarPoint → ℝ := fun q => Y i q.1
  have hY : ContDiff ℝ ∞ (Y i) :=
    (n04PositiveGeometry_reference_scalar_geometry (href i).1).1
  have hvalue : |g (f (x, p))| ≤ 1 := by
    have hσ := (G.matching (state x) hz hs i).geometry.inverse_maps_open hp
    have hy := ((href i).1.maps_open hσ).1
    change Y i (f (x, p)).1 ∈ Ioo (0 : ℝ) 1 at hy
    change |Y i (f (x, p)).1| ≤ 1
    rw [abs_of_pos hy.1]
    exact hy.2.le
  have houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f (x, p))‖ ≤ M := by
    intro j hj
    cases j with
    | zero =>
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hvalue.trans hM
    | succ j =>
        have hb : ‖iteratedFDeriv ℝ (j + 1) (Y i) (f (x, p)).1‖ ≤ Br * E ^ Br := by
          have hy := (hrefjets i j (by omega) (f (x, p)).1).1
          change |iteratedDeriv (j + 1) (Y i) (f (x, p)).1| ≤ Br * E ^ Br at hy
          simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
            hy
        exact (n04PositiveGeometry_norm_radial_pullback_le hY (j + 1) (f (x, p))).trans
          (hb.trans (hraise hBrD))
  have hinner (c : OrderedFinpartition n) (j : Fin c.length) :
      ‖JS.D (c.partSize j) (x, p) (v ∘ c.emb j)‖ ≤
        M * parameterHeightWeight H (w.restrict (c.emb j)).stateArity *
          t ^ n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb j)) offset :=
    (hraw c j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hraise hAD) (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))
  have hbound : ‖J.D n (x, p) v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      M * M ^ n * L ^ n * parameterHeightWeight H w.stateArity *
        t ^ n04PositiveGeometry_savedSpatialCost w offset :=
    n04PositiveGeometry_finiteKernel_savedSpatial_bound JS isOpen_univ
      (hY.comp contDiff_fst).contDiffOn (fun _ _ => mem_univ _) J hn w offset
      (x, p) ⟨hx, mem_univ _⟩ v (zero_le_one.trans hM) hM hH
      (hHR.trans (le_max_right _ _)) hL ht houter hinner
  have hcost : (Fintype.card (OrderedFinpartition n) : ℝ) * M * M ^ n * L ^ n ≤
      B * E ^ B := by
    calc
      _ = ((Fintype.card (OrderedFinpartition n) : ℝ) * L ^ n) * M ^ (n + 1) := by
        rw [pow_succ]
        ring
      _ ≤ (P * L ^ N) * M ^ (N + 1) := mul_le_mul
        (mul_le_mul (hcard n hnN) (pow_le_pow_right₀ hL hnN)
          (pow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hP))
        (pow_le_pow_right₀ hM (Nat.add_le_add_right hnN 1))
        (pow_nonneg (zero_le_one.trans hM) _)
        (mul_nonneg (zero_le_one.trans hP) (pow_nonneg (zero_le_one.trans hL) _))
      _ ≤ B₀ * E ^ B₀ := hpack E hE
      _ ≤ B * E ^ B := mul_le_mul hB₀B
        (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  simpa only [Real.norm_eq_abs] using hbound.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
