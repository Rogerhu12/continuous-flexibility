import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoefficientWords

/-!
# One actual sampled prefix for the four retained pullback coefficients

The finite inverse and composition constants are selected before the
component and state. The source tensors and forward slope already have
one common high denominator, so no additional angular shift is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

theorem n04PositiveGeometry_controlledCoefficient_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (G : N04PositiveGeometryControlledFamily W X 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          G.toN04PositiveGeometryControlData.coefficients
            (liftSectorParameter W.S W.C y.1) i side j y.2),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  let sourceData := n04PositiveGeometry_sourceForwardJet_sample_prefix W X hb hε hεW hεone hflow
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 heightData.choose
  have hL : 1 ≤ L := le_max_left _ _
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine ⟨sourceData.choose, sourceData.choose_spec.1, fun K => ?_⟩
  let prefixData := sourceData.choose_spec.2 K
  refine ⟨prefixData.choose, fun s => ?_⟩
  let orderData := prefixData.choose_spec s
  let As := orderData.choose
  let B := As + L
  have hAs : 1 ≤ As := orderData.choose_spec.1
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hAsB : As ≤ B := by dsimp only [B]; linarith
  have hLB : L ≤ B := by dsimp only [B]; linarith
  let N := K + s + 1
  let boundData (a : Fin 4) := n04PositiveGeometry_controlledCoefficient_word_bound
    G hb hεW hGb hGε N (a.val + 1) (by omega) (by omega) L hL
  let C := 1 + ∑ a : Fin 4, (boundData a).choose
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun a _ => zero_le_one.trans (boundData a).choose_spec.1))
  have haC (a : Fin 4) : (boundData a).choose ≤ C :=
    (Finset.single_le_sum (fun a _ => zero_le_one.trans (boundData a).choose_spec.1)
      (Finset.mem_univ a)).trans (le_add_of_nonneg_left zero_le_one)
  let degree := 1 + ∑ a : Fin 4, (boundData a).choose_spec.2.choose
  have haD (a : Fin 4) : (boundData a).choose_spec.2.choose ≤ degree := by
    have hsum : (boundData a).choose_spec.2.choose ≤
        ∑ b : Fin 4, (boundData b).choose_spec.2.choose :=
      Finset.single_le_sum (fun b _ => Nat.zero_le ((boundData b).choose_spec.2.choose))
        (Finset.mem_univ a)
    exact hsum.trans (Nat.le_add_left _ 1)
  let packData := n04PositiveGeometry_polynomial_sample_pack C B degree
  let A₀ := packData.choose
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx j hj hj4 Q z hz hzlow θ R hR hzR
  let idx : Fin 4 := ⟨j - 1, by omega⟩
  have hidx : idx.val + 1 = j := by dsimp only [idx]; omega
  let Q' := Q.congr (fun y _ => congrArg
    (fun n => G.toN04PositiveGeometryControlData.coefficients
      (liftSectorParameter W.S W.C y.1) i side n y.2) hidx.symm)
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + prefixData.choose * K : ℕ) : ℝ) + 1))
  let P := fun v => pairGrading (sectorGrading W.S) realGrading sourceData.choose v ≤ 1 ∧
    pairGrading (sectorGrading W.S) realGrading (sourceData.choose + s + prefixData.choose * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHL : H ≤ L := (heightData.choose_spec.2 i).2.trans (le_max_right _ _)
  have hBM : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hBM
  have hHM : H ≤ M := hHL.trans (hLB.trans hBM)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hsourceCost : As * E ^ As ≤ M :=
    mul_le_mul hAsB (Real.rpow_le_rpow_of_exponent_le hE hAsB)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  let JS (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :=
    n04PositiveGeometry_sourceForwardJet_joint W X hb hε hεW hεone hflow
      i side m hm hctx n hn hn4
  let Jβ := n04Realization_rootLabel_forwardJointDirections W.hT W.hS hN m (!side)
  let Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ =>
        deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2) :=
    (smoothDirections_angularIterate Jβ 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one])
  have hS (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
      N04BoundaryWordBounds (JS n hn hn4) K s 1 z θ P M H t prefixData.choose :=
    (orderData.choose_spec.2 i side m hm hctx n hn hn4 (JS n hn hn4) Jb
      z hz hzlow θ R hR hzR).1.enlarge hH (zero_le_one.trans ht) hsourceCost
  have hb' : N04BoundaryWordBounds Jb K s 1 z θ P M H t prefixData.choose :=
    (orderData.choose_spec.2 i side m hm hctx 1 le_rfl (by decide) (JS 1 le_rfl (by decide)) Jb
      z hz hzlow θ R hR hzR).2.enlarge hH (zero_le_one.trans ht) hsourceCost
  have hout := (boundData idx).choose_spec.2.choose_spec.2 i side m hm JS Jb Q'
    K s 1 le_rfl z hz θ P M H t hM hH hHL hHM ht prefixData.choose hS hb'
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    _ ≤ C * M ^ degree := mul_le_mul (haC idx) (pow_le_pow_right₀ hM (haD idx))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
    _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
    _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
