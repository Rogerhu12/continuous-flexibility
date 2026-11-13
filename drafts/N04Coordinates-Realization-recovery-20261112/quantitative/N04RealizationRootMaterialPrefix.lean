import ContinuousFlexibility.Analysis.N03RootEndpointMaterialJets
import ContinuousFlexibility.Analysis.N04RealizationRootJacobianMaterialBounds
import ContinuousFlexibility.Analysis.N04RealizationFiniteBoundaryEnvelopes

/-!
# A finite material prefix on the original root circles

The material root theorem and the actual Jacobian theorem are restricted
once to a common finite low-order neighborhood. The same atlas and host
sample remain in every bound. These numerical constants are selected
before any positive transport or endpoint-height correction is built.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

def N04RealizationRootMaterialPrefix
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (N base : ℕ) (ε K₀ C0 B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
    (∀ x ∈ Ioo (C.left m) (C.right m),
      K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
        -deriv D.w x / (x * D.w x)) →
    ∀ side : Bool, ∀ θ : ℝ,
      let r : ℝ := n01ComponentRoot C m side
      let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
      (r, θ) ∈ physicalPieceClosed S K z i ∧ 0 < K.height z i (r, θ) ∧
        (∀ n, 1 ≤ n → n ≤ N →
          ‖iteratedFDeriv ℝ n (K.chart z i) (r, θ)‖ ≤
            B * (C0 * T.E0 (T.sample j)) ^ B) ∧
        (∀ sign : Bool, ∀ n, n ≤ N →
          ‖iteratedFDeriv ℝ n
            (fun p => K.height z i p ^ (if sign then (-1 : ℝ) else 1)) (r, θ)‖ ≤
            B * (C0 * T.E0 (T.sample j)) ^ B) ∧
        |planeJacobian (K.chart z i) (r, θ)|⁻¹ ≤
          B * (C0 * T.E0 (T.sample j)) ^ B

private theorem finiteRoot_coefficient_mono
    {a b V W : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hV : 1 ≤ V) (hVW : V ≤ W) :
    a * V ^ a ≤ b * W ^ b := by
  have hW : 1 ≤ W := hV.trans hVW
  have hpow : V ^ a ≤ W ^ b :=
    (Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
      (Real.rpow_le_rpow_of_exponent_le hW hab)
  exact mul_le_mul hab hpow (Real.rpow_nonneg (zero_le_one.trans hV) _)
    (ha.trans hab)

/-- The actual finite forward, height-power and inverse-Jacobian costs
share one neighborhood and one sampled envelope before all indices. -/
theorem n04Realization_rootMaterial_finite_prefix
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK₀ : 0 < K₀) (N : ℕ) :
    ∃ C0 B : ℝ, ∃ newBase : ℕ, ∃ η : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧ 1 ≤ B ∧
      base ≤ newBase ∧ 0 < η ∧ η ≤ ε ∧
      N04RealizationRootMaterialPrefix D T S C K N newBase η K₀ C0 B := by
  classical
  obtain ⟨CF, bF, ell, ηF, hCF, hfloorF, hbF, _, hηF, hηFε, hraw⟩ :=
    n04b_actual_root_material_jets_of_component_optical hS hT hN hfield hA hB hK₀
  obtain ⟨BP, hBP, hplus⟩ := hraw 1
  obtain ⟨BM, hBM, hminus⟩ := hraw (-1)
  obtain ⟨CJ, BJ, bJ, ηJ, hCJ, hfloorJ, hBJ, hbJ, hηJ, hηJε, hJac⟩ :=
    n04Realization_rootJacobian_material_bound hS hT hN hfield hA hB hK₀
  let C0 : ℝ := max CF CJ
  let P : ℝ := 1 + BJ + ∑ n : Fin (N + 1), (BP n.val + BM n.val)
  let B : ℝ := 2 * P
  let newBase : ℕ := max bF (max bJ (N + ell))
  let η : ℝ := min (min ηF ηJ) (1 / 2)
  have hsum₀ : 0 ≤ ∑ n : Fin (N + 1), (BP n.val + BM n.val) :=
    Finset.sum_nonneg (fun n _ => add_nonneg (hBP n.val).le (hBM n.val).le)
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [hBJ, hsum₀]
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hP]
  have hJP : BJ ≤ P := by dsimp only [P]; linarith only [hsum₀]
  have hterm (n : ℕ) (hn : n ≤ N) : BP n ≤ P ∧ BM n ≤ P := by
    let i : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have ht : BP n + BM n ≤ ∑ k : Fin (N + 1), (BP k.val + BM k.val) :=
      Finset.single_le_sum
        (f := fun k : Fin (N + 1) => BP k.val + BM k.val)
        (fun k _ => add_nonneg (hBP k.val).le (hBM k.val).le) (Finset.mem_univ i)
    dsimp only [P]
    constructor <;> linarith only [ht, hBP n, hBM n, hBJ]
  have hbaseF : bF ≤ newBase := le_max_left _ _
  have hbaseJ : bJ ≤ newBase := (le_max_left _ _).trans (le_max_right _ _)
  have horder : N + ell ≤ newBase := (le_max_right _ _).trans (le_max_right _ _)
  have hηηF : η ≤ ηF := (min_le_left _ _).trans (min_le_left _ _)
  have hηηJ : η ≤ ηJ := (min_le_left _ _).trans (min_le_right _ _)
  have hη : 0 < η := lt_min (lt_min hηF hηJ) (by norm_num)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1
  have hWF (j : ℕ) : CF * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le
  have hWJ (j : ℕ) : CJ * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hE j).le
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) := (hfloorF j).trans (hWF j)
  refine ⟨C0, B, newBase, η, hCF.trans (le_max_left _ _), hfloor, hB,
    hbF.trans hbaseF, hη, hηηF.trans hηFε, ?_⟩
  intro z hz hs m j hhost hopt side θ
  have hzF := stateNeighborhood_mono S C hbaseF hηηF hz
  have hzJ := stateNeighborhood_mono S C hbaseJ hηηJ hz
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hsmall : pairGrading (stateGrading S) realGrading newBase
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hz).trans (by
      have he : η ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hfinite {a v : ℝ} {n : ℕ} (ha : 0 ≤ a) (haP : a ≤ P) (hn : n ≤ N)
      (hv : v ≤ a * (CF * T.E0 (T.sample j)) ^ a *
        (1 + pairGrading (stateGrading S) realGrading (n + ell)
          (z - (C.referenceState, 0)))) :
      v ≤ B * (C0 * T.E0 (T.sample j)) ^ B := by
    have hg : pairGrading (stateGrading S) realGrading (n + ell)
        (z - (C.referenceState, 0)) ≤ 1 :=
      (hp ((Nat.add_le_add_right hn ell).trans horder) _).trans hsmall
    calc
      v ≤ (a * (CF * T.E0 (T.sample j)) ^ a) * 2 :=
        hv.trans (mul_le_mul_of_nonneg_left (by linarith only [hg])
          (mul_nonneg ha (Real.rpow_nonneg (zero_le_one.trans (hfloorF j)) _)))
      _ ≤ (P * (C0 * T.E0 (T.sample j)) ^ P) * 2 :=
        mul_le_mul_of_nonneg_right (finiteRoot_coefficient_mono ha haP
          (hfloorF j) (hWF j)) (by norm_num)
      _ = B * (C0 * T.E0 (T.sample j)) ^ P := by dsimp only [B]; ring
      _ ≤ B * (C0 * T.E0 (T.sample j)) ^ B :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hfloor j) (by
            dsimp only [B]; linarith only [hP]))
          (zero_le_one.trans hB)
  have hplus' := hplus z hzF hs m j hhost hopt side θ
  have hminus' := hminus z hzF hs m j hhost hopt side θ
  refine ⟨hplus'.1, hplus'.2.1, ?_, ?_, ?_⟩
  · intro n hn hN
    exact hfinite (hBP n).le (hterm n hN).1 hN (hplus'.2.2.1 n hn)
  · intro sign n hN
    cases sign
    · exact hfinite (hBP n).le (hterm n hN).1 hN (hplus'.2.2.2 n)
    · exact hfinite (hBM n).le (hterm n hN).2 hN (hminus'.2.2.2 n)
  · exact (hJac z hzJ hs m j hhost hopt side θ).2.trans
      (finiteRoot_coefficient_mono (zero_le_one.trans hBJ)
        (hJP.trans (by dsimp only [B]; linarith only [hP]))
        (hfloorJ j) (hWJ j))

end ContinuousFlexibility.Analysis
