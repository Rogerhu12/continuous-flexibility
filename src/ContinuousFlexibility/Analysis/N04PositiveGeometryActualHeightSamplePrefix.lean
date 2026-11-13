import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceHeightSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaPrefix

/-!
# Sampled mixed derivatives of the stored positive height

The actual raw source traces now discharge the input of the established
controlled-height estimate. Its existing collar, logarithmic bound and
material envelope are reused for both `Q` and its literal reciprocal.
The same parameter prefix is retained through every spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_actualControlledHeight_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s → ∀ inv : Bool, ∀ q : PolarPoint,
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun y => mixedDerivative a b (fun p => if inv then
          (G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C y) i p)⁻¹
          else G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C y) i p) q),
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
      (∀ j, pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
      ‖J.D k x v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let sourceData := n04PositiveGeometry_sourceHeightChoice_sample_prefix W X hb hε hεW hεone hflow
  let low := sourceData.choose
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let RH := heightData.choose
  let p := pairGrading (sectorGrading W.S) realGrading
  refine ⟨low, sourceData.choose_spec.1, fun K => ?_⟩
  let shiftData := sourceData.choose_spec.2 K
  let shift := shiftData.choose
  refine ⟨shift, fun s => ?_⟩
  let sourceOrder := shiftData.choose_spec s
  let Araw := sourceOrder.choose
  let I := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  let outputData (j : I) := n04PositiveGeometry_controlledHeight_shifted_bound
    (V := StateDirections W.S × ℝ) G j.1.val j.2.1.val j.2.2.val RH Araw
  let B (j : I) := (outputData j).choose
  have hB (j : I) : 1 ≤ B j := (outputData j).choose_spec.1
  let A := 1 + ∑ j, B j
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j)))
  have hBA (j : I) : B j ≤ A :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨A, hA, ?_⟩
  intro i k hk a b hab inv q J x hx hxlow v hv R hR hxR hvR
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let E := W.U.E0 (W.U.sample (X.cell i))
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun z => p low z ≤ 1 ∧ p (low + s + shift * K + 1) z ≤ R
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHR : H ≤ RH := (heightData.choose_spec.2 i).2
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 0 ≤ Araw * E ^ Araw := mul_nonneg (zero_le_one.trans sourceOrder.choose_spec.1)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hP : P 0 := ⟨((p low).map_zero').trans_le zero_le_one,
    ((p (low + s + shift * K + 1)).map_zero').trans_le (zero_le_one.trans hR)⟩
  have htpow (d : ℕ) : t ^ d = R ^ ((d : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  let Jraw (side : Bool) (j : ℕ) (hj : j ≤ n) :=
    n04PositiveGeometry_sourceHeight_joint W X hb hε hεW hεone hflow hctx i side j (hj.trans hn)
  let JH (side : Bool) (j : ℕ) (hj : j ≤ n) (u : ℕ) (θ : ℝ) :=
    smoothDirections_angularStateSlice (Jraw side j hj) u θ
  have hraw (side : Bool) (j : ℕ) (hj : j ≤ n) (e : ℕ) (he : e ≤ k)
      (u : ℕ) (hu : u ≤ a + b) (θ : ℝ) (w : Fin e → (StateDirections W.S × ℝ))
      (hw : ∀ j, P (w j)) :
      ‖(JH side j hj u θ).D e x w‖ ≤ Araw * E ^ Araw * parameterHeightWeight H e *
        R ^ (((u + shift * e : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    let src := n04PositiveGeometry_source_some W X i side
    let m := src.choose
    have hm : (X.src i side).val = some m := src.choose_spec
    have hword := sourceOrder.choose_spec.2 i side m hm (hctx m (!side)) j (hj.trans hn)
      false (Jraw side j hj) x hx hxlow θ R hR hxR
    have hnorm := n04PositiveGeometry_boundaryWord_to_angular_reserve (Jraw side j hj)
      (smoothDirections_angularStateSlice (Jraw side j hj)) hx θ P hP hword
      e u (he.trans hk) (by omega) w hw
    have hpower : t ^ ((u - 1) + shift * e) ≤ t ^ (u + shift * e) :=
      pow_le_pow_right₀ ht (by omega)
    exact (hnorm.trans (mul_le_mul_of_nonneg_left hpower
      (mul_nonneg hM (parameterHeightWeight_nonneg hH e)))).trans_eq
        (congrArg (fun r : ℝ => Araw * E ^ Araw * parameterHeightWeight H e * r)
          (htpow (u + shift * e)))
  let idx : I := ⟨⟨k, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩⟩
  have hout := (outputData idx).choose_spec.2 (sectorNeighborhood W.S base ε ε)
    (sectorNeighborhood_isOpen W.S base ε ε) (liftSectorParameter W.S W.C)
    (fun y hy => stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy le_rfl))
    (fun y _ => hN.2.2.1.liftSectorParameter_sector y) i JH x hx P v
    (fun j => ⟨hv j, hvR j⟩) H R hH hHR hR (s + shift * K) shift hraw inv q J
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul (hBA idx)
      (Real.rpow_le_rpow_of_exponent_le hE (hBA idx))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA))
      (parameterHeightWeight_nonneg hH k)) (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
