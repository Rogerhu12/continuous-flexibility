module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootJacobian

/-!
# One material envelope for the genuine finite root fields

The finite state order is chosen once, before the negative component and its
host sample. The stored chart, stored height, its reciprocal and the reciprocal
Jacobian all obey one numerical material bound on that neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The raw fields used to estimate an actual relative endpoint map.
There is deliberately no zeroth-order bound on the chart's angular lift. -/
structure N04PositiveGeometryFiniteRootFields (N : ℕ)
    (F : PolarPoint → PolarPoint) (H : PolarPoint → ℝ) (r M : ℝ) : Prop where
  chart_jets : ∀ θ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ M
  height_jets : ∀ θ k, k ≤ N → ‖iteratedFDeriv ℝ k H (r, θ)‖ ≤ M
  inverse_height_jets : ∀ θ k, k ≤ N →
    ‖iteratedFDeriv ℝ k (fun p => (H p)⁻¹) (r, θ)‖ ≤ M
  inverse_jacobian : ∀ θ, |planeJacobian F (r, θ)|⁻¹ ≤ M

private theorem finite_root_material_small_state
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) {z : Z}
    {k N loss base : ℕ} (hk : k ≤ N) (hN : N + loss ≤ base)
    (hz : p base z ≤ 1) {A B V W v : ℝ}
    (hA : 0 ≤ A) (hAB : 2 * A ≤ B) (hV : 1 ≤ V) (hVW : V ≤ W)
    (hv : v ≤ A * V ^ A * (1 + p (k + loss) z)) :
    v ≤ B * W ^ B := by
  have hB : 0 ≤ B := by linarith
  have hA' : A ≤ B := by linarith
  have hW : 1 ≤ W := hV.trans hVW
  have hg : p (k + loss) z ≤ 1 :=
    (hp ((Nat.add_le_add_right hk loss).trans hN) z).trans hz
  have hpower : V ^ A ≤ W ^ B :=
    (Real.rpow_le_rpow (zero_le_one.trans hV) hVW hA).trans
      (Real.rpow_le_rpow_of_exponent_le hW hA')
  calc
    v ≤ A * V ^ A * (1 + p (k + loss) z) := hv
    _ ≤ A * V ^ A * (1 + 1) := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ)) hg)
      (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hV) _))
    _ = (2 * A) * V ^ A := by ring
    _ ≤ B * W ^ B := mul_le_mul hAB hpower (Real.rpow_nonneg (zero_le_one.trans hV) _) hB

/-- Every finite prefix of the original physical root fields has a uniform
sample cost. The reference state is included in the same neighborhood. -/
theorem n04PositiveGeometry_actual_root_finite_material_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK : 0 < K₀) (N : ℕ) :
    ∃ C0 : ℝ, ∃ newBase : ℕ, ∃ ε' B : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧ 1 ≤ B ∧
      ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ side : Bool,
        let r := n01ComponentRoot C m side
        let i := if side then (K.cutPair m).2 else (K.cutPair m).1
        N04PositiveGeometryFiniteRootFields N (K.chart z i) (K.height z i) r
          (B * (C0 * T.E0 (T.sample j)) ^ B) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  refine (n04b_actual_root_material_jets_of_component_optical hS hT hN hfield hA hB hK).elim ?_
  intro CM hM1
  refine hM1.elim ?_
  intro bM hM2
  refine hM2.elim ?_
  intro lM hM3
  refine hM3.elim ?_
  intro ηM hM4
  have hCM := hM4.1
  have hfloorM := hM4.2.1
  have hbM := hM4.2.2.1
  have hηM := hM4.2.2.2.2.1
  have hηMε := hM4.2.2.2.2.2.1
  have hjets := hM4.2.2.2.2.2.2
  refine (hjets 1).elim ?_
  intro A hAj
  have hApos := hAj.1
  have hchartHeight := hAj.2
  refine (hjets (-1)).elim ?_
  intro I hIj
  have hIpos := hIj.1
  have hheightInverse := hIj.2
  refine (n04PositiveGeometry_actual_root_jacobian_material_cost hS hT hN hfield hA hB hK).elim ?_
  intro CJ hJ1
  refine hJ1.elim ?_
  intro bJ hJ2
  refine hJ2.elim ?_
  intro ηJ hJ3
  refine hJ3.elim ?_
  intro P hJ4
  have hCJ := hJ4.1
  have hfloorJ := hJ4.2.1
  have hηJ := hJ4.2.2.2.1
  have hηJε := hJ4.2.2.2.2.1
  have hP := hJ4.2.2.2.2.2.1
  have hJac := hJ4.2.2.2.2.2.2
  let C0 : ℝ := max CM CJ
  let newBase : ℕ := max bM (max bJ (N + lM))
  let ε' : ℝ := min (min ηM ηJ) (1 / 2)
  let B : ℝ := 1 + P + ∑ k ∈ Finset.range (N + 1), (2 * A k + 2 * I k)
  have hterm (k : ℕ) : 0 ≤ 2 * A k + 2 * I k :=
    add_nonneg (mul_nonneg (by norm_num) (hApos k).le)
      (mul_nonneg (by norm_num) (hIpos k).le)
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), (2 * A k + 2 * I k) :=
    Finset.sum_nonneg fun k _ => hterm k
  have hBone : 1 ≤ B := by dsimp only [B]; linarith
  have hPB : P ≤ B := by dsimp only [B]; linarith
  have hAB (k : ℕ) (hk : k ≤ N) : 2 * A k ≤ B := by
    have ht : 2 * A k + 2 * I k ≤
        ∑ j ∈ Finset.range (N + 1), (2 * A j + 2 * I j) :=
      Finset.single_le_sum (fun j _ => hterm j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp only [B]
    linarith only [ht, hIpos k, hP]
  have hIB (k : ℕ) (hk : k ≤ N) : 2 * I k ≤ B := by
    have ht : 2 * A k + 2 * I k ≤
        ∑ j ∈ Finset.range (N + 1), (2 * A j + 2 * I j) :=
      Finset.single_le_sum (fun j _ => hterm j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp only [B]
    linarith only [ht, hApos k, hP]
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1
  have hWM (j : ℕ) : CM * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le
  have hWJ (j : ℕ) : CJ * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hE j).le
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) := (hfloorM j).trans (hWM j)
  refine ⟨C0, newBase, ε', B, hCM.trans (le_max_left _ _), hfloor,
    hbM.trans (le_max_left _ _), lt_min (lt_min hηM hηJ) (by norm_num),
    ((min_le_left _ _).trans (min_le_left _ _)).trans hηMε, hBone, ?_⟩
  intro z hz hs m j hhost hoptical side
  have hzM : z ∈ stateNeighborhood S C bM ηM :=
    stateNeighborhood_mono S C (le_max_left _ _)
      ((min_le_left _ _).trans (min_le_left _ _)) hz
  have hzJ : z ∈ stateNeighborhood S C bJ ηJ :=
    stateNeighborhood_mono S C ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_left _ _).trans (min_le_right _ _)) hz
  have hsmall : pairGrading (stateGrading S) realGrading newBase
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hz).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have horder : N + lM ≤ newBase := (le_max_right _ _).trans (le_max_right _ _)
  refine { chart_jets := ?_, height_jets := ?_, inverse_height_jets := ?_, inverse_jacobian := ?_ }
  · intro θ k hk hkN
    exact finite_root_material_small_state hp hkN horder hsmall
      (hApos k).le (hAB k hkN) (hfloorM j) (hWM j)
      ((hchartHeight z hzM hs m j hhost hoptical side θ).2.2.1 k hk)
  · intro θ k hkN
    have hj := (hchartHeight z hzM hs m j hhost hoptical side θ).2.2.2 k
    have hj' := finite_root_material_small_state hp hkN horder hsmall
      (hApos k).le (hAB k hkN) (hfloorM j) (hWM j) hj
    simpa only [Real.rpow_one] using hj'
  · intro θ k hkN
    have hj := (hheightInverse z hzM hs m j hhost hoptical side θ).2.2.2 k
    have hj' := finite_root_material_small_state hp hkN horder hsmall
      (hIpos k).le (hIB k hkN) (hfloorM j) (hWM j) hj
    simpa only [Real.rpow_neg_one] using hj'
  · intro θ
    exact (hJac z hzJ hs m j hhost hoptical side θ).trans
      (mul_le_mul hPB
        ((Real.rpow_le_rpow (zero_le_one.trans (hfloorJ j)) (hWJ j)
          (zero_le_one.trans hP)).trans
          (Real.rpow_le_rpow_of_exponent_le (hfloor j) hPB))
        (Real.rpow_nonneg (zero_le_one.trans (hfloorJ j)) _) (zero_le_one.trans hBone))

end ContinuousFlexibility.Analysis
