import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinateDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryTransportMixedSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledReferenceInverse

/-!
# The sampled inverse chart at its fixed reference point

The fixed radial inverse changes only the material envelope. Its genuine
mixed parameter jets retain the original transport prefix, including the
coefficient one in the spatial contribution to the high index.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_controlledReferenceInverse_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    {base : ℕ} {ε : ℝ}
    (JT : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2))
    (hprefix : N04PositiveGeometryTransportSamplePrefix F false base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w), ∀ angle : Bool,
      ∀ k : ℕ, 0 < k → k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ CanonicalGeometry.unitStrip,
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun x => mixedDerivative a b (fun p =>
          n04PositiveGeometry_controlledReferenceComponent F Y true angle i
            (liftSectorParameter W.S W.C x) p) q),
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
      (∀ j, pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let rawData := n04PositiveGeometry_transport_projected_mixed_sample_prefix F false JT hprefix
  let low := rawData.choose
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  have hc := (sectorNeighborhood_convex W.S base ε ε).prod (convex_univ : Convex ℝ (univ : Set PolarPoint))
  refine ⟨low, rawData.choose_spec.1, fun K => ?_⟩
  let sd := rawData.choose_spec.2 K
  let shift := sd.choose
  refine ⟨shift, fun s => ?_⟩
  let rd := sd.choose_spec s
  let Araw := rd.choose
  let I := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  let outputData (j : I) := n04PositiveGeometry_controlledReferenceInverse_shifted_bound
    (V := StateDirections W.S × ℝ) F Y H₀ href hmaterial
      j.1.val j.2.1.val j.2.2.val rd.choose_spec.1
  let B (j : I) := (outputData j).choose
  have hB (j : I) : 1 ≤ B j := (outputData j).choose_spec.1
  let A := 1 + ∑ j, B j
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j)))
  have hBA (j : I) : B j ≤ A :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨A, hA, ?_⟩
  intro i angle k hk hkK a b hab q hq J x hx hxlow v hv R hR hxR hvR
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let E := W.U.E0 (W.U.sample (X.cell i))
  have hH : 0 ≤ H := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let L : PolarPoint →L[ℝ] ℝ := if angle then
    ContinuousLinearMap.snd ℝ ℝ ℝ else ContinuousLinearMap.fst ℝ ℝ ℝ
  have hL : ‖L‖ ≤ 1 := by
    cases angle
    · exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
    · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  let JC : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint => if angle then
        (F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2).2
        else (F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2).1) :=
    (smoothDirections_postcompCLM (JT i) L).congrOn (fun _ _ => by cases angle <;> rfl)
  let RF := n04Realization_jointMixedRegularity JC hU isOpen_univ hc
  have hraw (u w : ℕ) (huw : u + w ≤ a + b) (p : PolarPoint)
      (hp : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) :
      |(RF.parameter u w p (mem_univ _)).D k x v| ≤
        Araw * E ^ Araw * parameterHeightWeight H k *
          R ^ (((u + w + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    let Q : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun y => mixedDerivative u w (fun p => L
          (F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C y) i p)) p) :=
      (RF.parameter u w p (mem_univ _)).congrOn (fun y _ =>
        congrArg (fun f : PolarPoint → ℝ => mixedDerivative u w f p) (by
          funext p
          cases angle <;> rfl))
    exact rd.choose_spec.2 i L hL k hk hkK u w (huw.trans hab) p hp Q
      x hx hxlow v hv R hR hxR hvR
  let idx : I := ⟨⟨k, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩⟩
  have hout := (outputData idx).choose_spec.2 (sectorNeighborhood W.S base ε ε)
    (liftSectorParameter W.S W.C) i angle RF x hx v H R hH hR (s + shift * K) shift
      hraw q hq J
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul (hBA idx)
      (Real.rpow_le_rpow_of_exponent_le hE (hBA idx))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA))
      (parameterHeightWeight_nonneg hH k)) (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
