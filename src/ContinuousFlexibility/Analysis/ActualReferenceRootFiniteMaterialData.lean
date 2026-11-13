import ContinuousFlexibility.Analysis.ActualReferenceRootSlopeNormalization
import ContinuousFlexibility.Analysis.N03RootEndpointMaterialJets
import ContinuousFlexibility.Analysis.N04bActualAtlasInteriorCompletion
import ContinuousFlexibility.Analysis.OneSidedBoundaryJets
import ContinuousFlexibility.Analysis.N04bReferenceActualTravel

/-!
# Actual finite reference data with a material envelope

The true reference state removes the state grading from the original
stored root jets. The exact unit-density normalization supplies the
inverse inward slope from the height squared and the fixed profile.
A finite sum gives the raw coefficients and the two positive lower
bounds needed by the displayed reference Taylor width. The optical
lower condition remains explicit on the same negative component/host.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- One material base precedes the finite order. The resulting numerical
envelope precedes every component, original host and root orientation.
It controls exactly the raw radial data used by reference interpolation. -/
theorem n04Coordinates_actual_reference_root_finite_material_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (hK : 0 < K₀) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ side : Bool,
        let K := n04bActualTypedAtlas hT hS hN hfield e
        let k := e.symm (.inl (m, side))
        let c := if side then C.right m else C.left m
        let σ : ℝ := if side then -1 else 1
        let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
        let M := B * (C0 * T.E0 (T.sample j)) ^ B
        1 ≤ M ∧
          M⁻¹ ≤ σ * deriv (fun r : ℝ => (K.chart z₀ k (r, 0)).1) c ∧
          M⁻¹ ≤ K.height z₀ k (c, 0) ∧
          (∀ n : ℕ, 1 ≤ n → n ≤ N →
            |radialBoundaryJet (fun p => (K.chart z₀ k p).1) c n 0| ≤ M) ∧
          ∀ n : ℕ, n ≤ N → |radialBoundaryJet (K.height z₀ k) c n 0| ≤ M := by
  classical
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA := n04bWithInteriorDivision_partA
    (n04b_actualTypedAtlas_partA hT hS hN hfield e)
  have hB := n04bActualTypedAtlas_interiorCompletion_partB hT hS hN hfield e
  refine (n04b_actual_root_material_jets_of_component_optical hS hT hN hfield hA hB hK).elim ?_
  intro C0 hJ1
  refine hJ1.elim ?_
  intro newBase hJ2
  refine hJ2.elim ?_
  intro outLoss hJ3
  refine hJ3.elim ?_
  intro η hJ4
  have hC0 := hJ4.1
  have hfloor := hJ4.2.1
  have hη := hJ4.2.2.2.2.1
  have hjet := hJ4.2.2.2.2.2.2
  refine (hjet 1).elim ?_
  intro A hAj
  have hApos := hAj.1
  have hjetA := hAj.2
  refine (hjet (-1)).elim ?_
  intro I hIj
  have hIpos := hIj.1
  have hjetI := hIj.2
  refine (hjet 2).elim ?_
  intro Q hQj
  have hQpos := hQj.1
  have hjetQ := hQj.2
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  have href : z₀ ∈ stateNeighborhood S C newBase η :=
    reference_mem_stateNeighborhood S C newBase hη
  have hsref : stateSector S z₀.1 := n04b_referenceState_sector hN.1.1.2.2.1
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨W₀, hW₀⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b))
    .exists_bound_of_continuousOn hD.2.2.1.1.continuous.continuousOn
  let V : ℝ := max W₀ 1
  have hV : 0 ≤ V := zero_le_one.trans (le_max_right _ _)
  have hwbound (r : ℝ) (hr : r ∈ Icc D.a D.b) : D.w r ≤ V :=
    (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hW₀ r hr).trans
      (le_max_left _ _))
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro N
  let J : ℝ := ∑ n ∈ Finset.range (N + 1), A n
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun n _ => (hApos n).le)
  let B : ℝ := 1 + J + I 0 + Q 0 + V * Q 0
  have hVQ : 0 ≤ V * Q 0 := mul_nonneg hV (hQpos 0).le
  have hBone : 1 ≤ B := by dsimp only [B]; linarith only [hJ, hIpos 0, hQpos 0, hVQ]
  have hIB : I 0 ≤ B := by dsimp only [B]; linarith only [hJ, hQpos 0, hVQ]
  have hQB : Q 0 ≤ B := by dsimp only [B]; linarith only [hJ, hIpos 0, hVQ]
  have hVQB : V * Q 0 ≤ B := by dsimp only [B]; linarith only [hJ, hIpos 0, hQpos 0]
  have hAB (n : ℕ) (hn : n ≤ N) : A n ≤ B := by
    have hAn : A n ≤ J :=
      Finset.single_le_sum (f := A) (fun k _ => (hApos k).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [B]
    linarith only [hAn, hIpos 0, hQpos 0, hVQ]
  refine ⟨B, hBone, ?_⟩
  intro m j hhost hoptical side
  let k := e.symm (.inl (m, side))
  let c := if side then C.right m else C.left m
  let σ : ℝ := if side then -1 else 1
  let W : ℝ := C0 * T.E0 (T.sample j)
  let M : ℝ := B * W ^ B
  have hW : 1 ≤ W := hfloor j
  have hM : 1 ≤ M := by
    exact one_le_mul_of_one_le_of_one_le hBone (Real.one_le_rpow hW (zero_le_one.trans hBone))
  have hcost {a b : ℝ} (ha : a ≤ B) (hb : b ≤ B) : b * W ^ a ≤ M :=
    mul_le_mul hb (Real.rpow_le_rpow_of_exponent_le hW ha)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hBone)
  have hi : (if side then ((n04bActualTypedAtlas hT hS hN hfield e).cutPair m).2
      else ((n04bActualTypedAtlas hT hS hN hfield e).cutPair m).1) = k := by
    cases side <;> rfl
  have hja := hjetA z₀ href hsref m j hhost hoptical side 0
  have hji := hjetI z₀ href hsref m j hhost hoptical side 0
  have hjq := hjetQ z₀ href hsref m j hhost hoptical side 0
  have hFbound (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (K.chart z₀ k) (c, 0)‖ ≤ A n * W ^ (A n) := by
    simpa only [n04bWithInteriorDivision, n01ComponentRoot, hi, z₀, sub_self,
      map_zero, add_zero, mul_one] using hja.2.2.1 n hn
  have hHbound (n : ℕ) :
      ‖iteratedFDeriv ℝ n (K.height z₀ k) (c, 0)‖ ≤ A n * W ^ (A n) := by
    simpa only [n04bWithInteriorDivision, n01ComponentRoot, hi, z₀, sub_self,
      map_zero, add_zero, mul_one, Real.rpow_one] using hja.2.2.2 n
  have hroot := n04Coordinates_actual_reference_negative_endpoint_data hT hS hN hfield e m side
  have hopen := n04Coordinates_actual_reference_negative_radial_fields hT hS hN hfield e m side
  have hHpos : 0 < K.height z₀ k (c, 0) := (hroot.1 0).2.2.2.1
  have hHinv : (K.height z₀ k (c, 0))⁻¹ ≤ I 0 * W ^ (I 0) := by
    have h0 : |K.height z₀ k (c, 0)|⁻¹ ≤ I 0 * W ^ (I 0) := by
      simpa only [n04bWithInteriorDivision, n01ComponentRoot, hi, z₀, sub_self,
        map_zero, add_zero, mul_one, norm_iteratedFDeriv_zero, Real.rpow_neg_one,
        norm_inv, Real.norm_eq_abs] using hji.2.2.2 0
    rwa [abs_of_pos hHpos] at h0
  have hHsquare : K.height z₀ k (c, 0) ^ 2 ≤ Q 0 * W ^ (Q 0) := by
    simpa only [n04bWithInteriorDivision, n01ComponentRoot, hi, z₀, sub_self,
      map_zero, add_zero, mul_one, norm_iteratedFDeriv_zero, Real.rpow_two,
      Real.norm_of_nonneg (sq_nonneg _)] using hjq.2.2.2 0
  have hcD : c ∈ Icc D.a D.b := by
    have hc := (hN.1.1.2.2.2.1.1 m)
    cases side
    · exact ⟨hc.1.le, (hc.2.1.trans hc.2.2).le⟩
    · exact ⟨(hc.1.trans hc.2.1).le, hc.2.2.le⟩
  have hqinverse :
      (σ * deriv (fun r : ℝ => (K.chart z₀ k (r, 0)).1) c)⁻¹ ≤ M := by
    rw [(n04Coordinates_actual_reference_root_slope_normalization hT hS hN hfield e m side).2]
    calc
      _ ≤ K.height z₀ k (c, 0) ^ 2 * V :=
        mul_le_mul_of_nonneg_left (hwbound c hcD) (sq_nonneg _)
      _ ≤ (Q 0 * W ^ (Q 0)) * V := mul_le_mul_of_nonneg_right hHsquare hV
      _ = (V * Q 0) * W ^ (Q 0) := by ring
      _ ≤ M := hcost hQB hVQB
  have hinv_lower {x : ℝ} (hx : 0 < x) (hi : x⁻¹ ≤ M) : M⁻¹ ≤ x := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hx) hi
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hc : c ∈ Icc (C.left m) (C.right m) := by
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  refine ⟨hM, hinv_lower hroot.2 hqinverse,
    hinv_lower hHpos (hHinv.trans (hcost hIB hIB)), ?_, ?_⟩
  · intro n hn hNn
    have hm := abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
      hab hopen.1.fst hc (hroot.1 0).1.fst n 0
    have hproj := (ContinuousLinearMap.fst ℝ ℝ ℝ).norm_iteratedFDeriv_comp_left
      (hroot.1 0).1 (n := n) (by simp)
    have hnorm : ‖iteratedFDeriv ℝ n (fun p => (K.chart z₀ k p).1) (c, 0)‖ ≤
        ‖iteratedFDeriv ℝ n (K.chart z₀ k) (c, 0)‖ :=
      hproj.trans (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..))
    have hrad : |radialBoundaryJet (fun p => (K.chart z₀ k p).1) c n 0| ≤
        ‖iteratedFDeriv ℝ n (fun p => (K.chart z₀ k p).1) (c, 0)‖ := by
      simpa only [mixedDerivative, radialBoundaryJet, iteratedDeriv_zero, Nat.add_zero] using hm
    exact hrad.trans (hnorm.trans ((hFbound n hn).trans (hcost (hAB n hNn) (hAB n hNn))))
  · intro n hNn
    have hm := abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
      hab hopen.2.1 hc (hroot.1 0).2.1 n 0
    have hrad : |radialBoundaryJet (K.height z₀ k) c n 0| ≤
        ‖iteratedFDeriv ℝ n (K.height z₀ k) (c, 0)‖ := by
      simpa only [mixedDerivative, radialBoundaryJet, iteratedDeriv_zero, Nat.add_zero] using hm
    exact hrad.trans ((hHbound n).trans (hcost (hAB n hNn) (hAB n hNn)))

end ContinuousFlexibility.Analysis
