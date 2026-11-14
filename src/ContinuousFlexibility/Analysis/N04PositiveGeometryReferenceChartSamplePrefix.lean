module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinateDirections
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledReferenceChart
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSampleHeight

/-!
# The sampled forward chart on the physical positive slab

The fixed reference radial chart is composed with the actual inverse
transport using its saved partition budget. The angular component is a
linear projection of that same transport. Both retain the same sample,
low base, parameter prefix and final spatial exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_controlledReferenceChart_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    {base : ℕ} {ε : ℝ} (hFb : F.base ≤ base) (hFε : ε ≤ F.ε)
    (JS : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2))
    (hprefix : N04PositiveGeometryTransportSamplePrefix F true base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w), ∀ angle : Bool,
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          n04PositiveGeometry_controlledReferenceComponent F Y false angle i
            (liftSectorParameter W.S W.C z.1) z.2),
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
      ∀ q ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ),
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ K + s + 1 →
      ∀ w : StateAngleWord n, 0 < w.stateArity → w.stateArity ≤ K →
      ∀ v : Fin n → (StateDirections W.S × ℝ) × PolarPoint,
      (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j).1 ≤ 1 ∧
        pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j).1 ≤ R ∧
        ‖(v j).2‖ ≤ 1) →
      |J.D n (x, q) v| ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) w.stateArity *
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) ^
          (w.angleArity + shift * w.stateArity) := by
  classical
  let low := hprefix.choose
  let heightData := n04PositiveGeometry_sample_height_bound W X (by norm_num : (0 : ℝ) < 3 / 4)
  let RH := heightData.choose
  refine ⟨low, hprefix.choose_spec.1, fun K => ?_⟩
  let sd := hprefix.choose_spec.2 K
  let shift := sd.choose
  refine ⟨shift, fun s => ?_⟩
  let rd := sd.choose_spec s
  let Araw := rd.choose
  let radialData := n04PositiveGeometry_controlledReferenceChart_radial_saved_bound
    (V := StateDirections W.S × ℝ) F Y H₀ href hmaterial (K + s + 1) Araw RH
  let B := max Araw radialData.choose
  have hB : 1 ≤ B := rd.choose_spec.1.trans (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro i angle J x hx hxlow q hq R hR hxR n hn hnN w hwpos hwK v hpure hbox
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let E := W.U.E0 (W.U.sample (X.cell i))
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHR : H ≤ RH := (heightData.choose_spec.2 i).2
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hraise {A : ℝ} (hAB : A ≤ B) : A * E ^ A ≤ B * E ^ B :=
    mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  cases angle with
  | false =>
      have hraw (c : OrderedFinpartition n) (j : Fin c.length) :
          ‖(JS i).D (c.partSize j) (x, q) (v ∘ c.emb j)‖ ≤
            Araw * E ^ Araw * parameterHeightWeight H (w.restrict (c.emb j)).stateArity *
              t ^ n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb j)) shift := by
        have harity : (w.restrict (c.emb j)).stateArity ≤ K :=
          ((Finset.single_le_sum (fun l _ => Nat.zero_le (w.restrict (c.emb l)).stateArity)
            (Finset.mem_univ j)).trans_eq (w.sum_restrict_stateArity c)).trans hwK
        have hr := rd.choose_spec.2 i (JS i) x hx hxlow q hq R hR hxR
          (c.partSize j) (c.partSize_pos j) ((c.partSize_le j).trans hnN)
          (w.restrict (c.emb j)) harity (v ∘ c.emb j)
          (fun l => by simpa only [StateAngleWord.isState_restrict, Function.comp_apply]
            using hpure (c.emb j l)) (fun l => hbox (c.emb j l))
        have hpower : (w.restrict (c.emb j)).angleArity +
            shift * (w.restrict (c.emb j)).stateArity - 1 ≤
              n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb j)) shift := by
          unfold n04PositiveGeometry_savedSpatialCost
          split_ifs with h
          · simp only [h, Nat.mul_zero, Nat.add_zero, le_refl]
          · exact Nat.sub_le _ _
        exact hr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hpower)
          (mul_nonneg (mul_nonneg (zero_le_one.trans rd.choose_spec.1)
            (Real.rpow_nonneg (zero_le_one.trans hE) _)) (parameterHeightWeight_nonneg hH _)))
      have hout := radialData.choose_spec.2 (sectorNeighborhood W.S base ε ε)
        (liftSectorParameter W.S W.C) i (JS i) J n hn hnN w shift x hx
        (stateNeighborhood_mono W.S W.C hFb hFε
          (liftSectorParameter_mem_stateNeighborhood (C := W.C) hx le_rfl))
        (W.through03.1.1.2.2.1.liftSectorParameter_sector x) q hq v H t hH hHR ht hraw
      have hcost : radialData.choose * E ^ radialData.choose * parameterHeightWeight H w.stateArity *
          t ^ n04PositiveGeometry_savedSpatialCost w shift ≤
            B * E ^ B * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity) := by
        simp only [n04PositiveGeometry_savedSpatialCost, Nat.ne_of_gt hwpos, if_false]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hraise (le_max_right _ _))
            (parameterHeightWeight_nonneg hH _)) (pow_nonneg (zero_le_one.trans ht) _)
      exact hout.trans hcost
  | true =>
      let JP := smoothDirections_postcompCLM (JS i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      have heval : J.D n (x, q) v = ((JS i).D n (x, q) v).2 :=
        (congrArg (fun A => A v) (J.unique JP n (x, q) ⟨hx, mem_univ _⟩)).trans
          (smoothDirections_postcompCLM_D_apply (JS i) (ContinuousLinearMap.snd ℝ ℝ ℝ) n (x, q) v)
      have hproj : |J.D n (x, q) v| ≤ ‖(JS i).D n (x, q) v‖ :=
        (congrArg abs heval).trans_le (by simpa only [Real.norm_eq_abs] using norm_snd_le ((JS i).D n (x, q) v))
      have hr := rd.choose_spec.2 i (JS i) x hx hxlow q hq R hR hxR n hn hnN w hwK v hpure hbox
      exact (hproj.trans hr).trans (mul_le_mul
        (mul_le_mul_of_nonneg_right (hraise (le_max_left _ _)) (parameterHeightWeight_nonneg hH _))
        (pow_le_pow_right₀ ht (Nat.sub_le _ _)) (pow_nonneg (zero_le_one.trans ht) _)
        (mul_nonneg (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (zero_le_one.trans hE) _))
          (parameterHeightWeight_nonneg hH _)))

end ContinuousFlexibility.Analysis
