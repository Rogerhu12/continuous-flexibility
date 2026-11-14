module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceAllOrderMaterialJets
public import ContinuousFlexibility.Analysis.PositiveReferencePrescribedCosts
public import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
public import ContinuousFlexibility.Analysis.CircleInverseDerivativeBounds

/-!
# Inverse jets of the same displayed positive reference coordinate

The low finite envelope and the Taylor width are selected once, before
all spatial orders. The genuine two-sided inverse of that same integral
coordinate has polynomial material jets. Forward coordinate and height
bounds are retained for the same choice. No global zeroth inverse-value
bound is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem referenceScalarInverse_finiteJet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M : ℝ}, 1 ≤ M →
      ∀ f g : ℝ → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ x, f (g x) = x) → (∀ x, g (f x) = x) →
      (∀ x, |deriv g x| ≤ M) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x, |iteratedDeriv (k + 1) f x| ≤ M) →
      ∀ x, |iteratedDeriv (N + 1) g x| ≤ C * M ^ d := by
  obtain ⟨C, hC, d, hbound⟩ :=
    exists_nonlinearInverse_finiteJet_polynomial_envelope (E := ℝ) (F := ℝ) N
  refine ⟨C, hC, d, ?_⟩
  intro M hM f g hf hg hright hleft hfirst hraw x
  have he : g ∘ f = id := funext hleft
  have hL : (fderiv ℝ g x).comp (fderiv ℝ f (g x)) =
      ContinuousLinearMap.id ℝ ℝ := by
    calc
      _ = (fderiv ℝ g (f (g x))).comp (fderiv ℝ f (g x)) := by rw [hright x]
      _ = fderiv ℝ (g ∘ f) (g x) :=
        (fderiv_comp (g x) (hg.differentiable (by simp) _)
          (hf.differentiable (by simp) _)).symm
      _ = _ := by rw [he, fderiv_id]
  have hfirst' : ‖fderiv ℝ g x‖ ≤ M := by
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
    exact hfirst x
  have hraw' (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
      ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      hraw k hk hkN (g x)
  have hb := hbound hM f g x hf.contDiffAt hg.contDiffAt
    (Eventually.of_forall hright) (fderiv ℝ g x) hL hfirst' hraw'
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb

theorem n04Coordinates_retained_positive_reference_inverse_material_jets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e : ℕ ≃ N04PieceIndex Γ.reference) (hK : 0 < K)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x)) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ n : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      (∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
      ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
        let A := n04bActualTypedAtlas hT hS hN hfield e
        let W := C0 * T.E0 (T.sample j)
        let U := B * W ^ B
        let δ := positiveReferenceTaylorWidth n
          (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
        let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src side) A)
        let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src side) A)
        let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
          (deriv (ys false)) (deriv (ys true))
        let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
          (hs false) (hs true)
        (∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv (k + 1) Y x| ≤ M * W ^ M ∧
          |iteratedDeriv k H x| ≤ M * W ^ M ∧
          |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ M * W ^ M) ∧
        ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun Y) x| ≤ M * W ^ M := by
  obtain ⟨C0, hC0, hfloor, hfamily⟩ :=
    n04Coordinates_retained_positive_reference_allOrder_material_jets
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e hK hhost hoptical
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro n
  obtain ⟨B, hB, hfinite, hforward⟩ := hfamily n
  refine ⟨B, hB, hfinite, ?_⟩
  intro N
  obtain ⟨A0, hA0, hforwardN⟩ := hforward N
  obtain ⟨C1, hC1, d, hinverse⟩ := referenceScalarInverse_finiteJet_envelope N
  let D : ℝ := 1 + A0 + 2 * B
  let coefficient : ℝ := C1 * D ^ d
  let exponent : ℝ := D * (d : ℝ)
  let M : ℝ := 1 + D + coefficient + exponent
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hA0, hB]
  have hA0D : A0 ≤ D := by dsimp only [D]; linarith only [hB]
  have hBD : B ≤ D := by dsimp only [D]; linarith only [hA0, hB]
  have htwoBD : 2 * B ≤ D := by dsimp only [D]; linarith only [hA0]
  have hcoefficient : 0 < coefficient :=
    mul_pos (zero_lt_one.trans_le hC1) (pow_pos (zero_lt_one.trans_le hD) _)
  have hexponent : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hD) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hD, hcoefficient, hexponent]
  have hDM : D ≤ M := by dsimp only [M]; linarith only [hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by dsimp only [M]; linarith only [hD, hexponent]
  have hexponentM : exponent ≤ M := by dsimp only [M]; linarith only [hD, hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let W : ℝ := C0 * T.E0 (T.sample j)
  let U : ℝ := B * W ^ B
  let V : ℝ := D * W ^ D
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (src side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (src side)
  let y : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceCoordinate (src side) A
  let h : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceHeight (src side) A
  let δ := positiveReferenceTaylorWidth n (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (h side)
  let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
    (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
    (hs false) (hs true)
  let χ : ℝ → ℝ := Function.invFun Y
  have hW : 1 ≤ W := hfloor j
  have hV : 1 ≤ V := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ D * W ^ D := mul_le_mul hD (Real.one_le_rpow hW (zero_le_one.trans hD))
        zero_le_one (zero_le_one.trans hD)
  have hrawcost : A0 * W ^ A0 ≤ V := by
    calc
      _ ≤ A0 * W ^ D := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hA0D) (zero_le_one.trans hA0)
      _ ≤ D * W ^ D := mul_le_mul_of_nonneg_right hA0D
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hlowcost : 2 * U ≤ V := by
    calc
      _ = (2 * B) * W ^ B := by dsimp only [U]; ring
      _ ≤ (2 * B) * W ^ D := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hBD)
        (mul_nonneg (by norm_num) (zero_le_one.trans hB))
      _ ≤ D * W ^ D := mul_le_mul_of_nonneg_right htwoBD
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hfinalcost : V ≤ M * W ^ M := by
    calc
      _ ≤ D * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hDM) (zero_le_one.trans hD)
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hDM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hinversecost : C1 * V ^ d ≤ M * W ^ M := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [V, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) D d]
        ring
      _ ≤ coefficient * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hexponentM) hcoefficient.le
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hcoefficientM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hinput := hfinite i j hmid src
  have hU : 1 ≤ U := hinput.1
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hDgeom := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv Γ.reference.w) := hDgeom.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) :=
    n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src side)
  have hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 :=
    (positiveReferenceFiniteRadialJets_prescribed n
      (κ := U⁻¹) (M := U) (a := a) (b := b) (y := y) (h := h)
      hlr (inv_pos.mpr hUpos) hUpos.le
      (fun side => (hd side).1) (fun side => (hd side).2.1)
      (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
      (fun side => (hd side).2.2.2.2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      (fun side => (hinput.2.2.2 side).2.2.1)
      (fun side => (hinput.2.2.2 side).2.2.2)).1
  have hdercost : ∀ x, 0 < deriv Y x ∧ (deriv Y x)⁻¹ ≤ 2 * U := by
    have hc := positiveReferenceFiniteRadialJets_prescribed_costs n
      (κ := U⁻¹) (M := U) (U := U) (a := a) (b := b) (y := y) (h := h)
      hlr (inv_pos.mpr hUpos) hUpos.le hU le_rfl (inv_inv U).le
      hinput.2.1 hinput.2.2.1
      (fun side => (hd side).1) (fun side => (hd side).2.1)
      (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
      (fun side => (hd side).2.2.2.2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      (fun side => (hinput.2.2.2 side).2.2.1)
      (fun side => (hinput.2.2.2 side).2.2.2)
    intro x
    exact ⟨(hc.2.2.2 x).1, (hc.2.2.2 x).2.2.1⟩
  have hY : ContDiff ℝ ∞ Y := by
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (positiveReferenceCylinderChart Y (t, 0)).1) :=
      contDiff_fst.comp (hgeometry.chart_smooth.comp (contDiff_id.prodMk contDiff_const))
    simpa only [positiveReferenceCylinderChart] using hc
  have hχ : ContDiff ℝ ∞ χ := by
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (positiveReferenceCylinderInverse Y (t, 0)).1) :=
      contDiff_fst.comp (hgeometry.inverse_smooth.comp (contDiff_id.prodMk contDiff_const))
    simpa only [positiveReferenceCylinderInverse] using hc
  have hright (x : ℝ) : Y (χ x) = x := congrArg Prod.fst (hgeometry.right_inverse (x, 0))
  have hleft (x : ℝ) : χ (Y x) = x := congrArg Prod.fst (hgeometry.left_inverse (x, 0))
  have hfirst (x : ℝ) : |deriv χ x| ≤ V := by
    have he : deriv χ x = (deriv Y (χ x))⁻¹ :=
      (HasDerivAt.of_local_left_inverse hχ.continuous.continuousAt
        (hY.differentiable (by simp) (χ x)).hasDerivAt (hdercost (χ x)).1.ne'
        (Eventually.of_forall hright)).deriv
    rw [he, abs_of_pos (inv_pos.mpr (hdercost (χ x)).1)]
    exact (hdercost (χ x)).2.trans hlowcost
  have hactual : ∀ k, k ≤ N → ∀ x : ℝ,
      |iteratedDeriv (k + 1) Y x| ≤ A0 * W ^ A0 ∧
      |iteratedDeriv k H x| ≤ A0 * W ^ A0 ∧
      |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ A0 * W ^ A0 :=
    hforwardN i j hmid src
  have hi : ∀ x : ℝ, |iteratedDeriv (N + 1) χ x| ≤ C1 * V ^ d :=
    hinverse hV Y χ hY hχ hright hleft hfirst
      (fun k _ hkN x => (hactual k hkN x).1.trans hrawcost)
  change (∀ k, k ≤ N → ∀ x : ℝ,
    |iteratedDeriv (k + 1) Y x| ≤ M * W ^ M ∧
    |iteratedDeriv k H x| ≤ M * W ^ M ∧
    |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ M * W ^ M) ∧
    ∀ x : ℝ, |iteratedDeriv (N + 1) χ x| ≤ M * W ^ M
  refine ⟨?_, fun x => (hi x).trans hinversecost⟩
  intro k hk x
  have hb := hactual k hk x
  exact ⟨hb.1.trans (hrawcost.trans hfinalcost),
    hb.2.1.trans (hrawcost.trans hfinalcost), hb.2.2.trans (hrawcost.trans hfinalcost)⟩

end ContinuousFlexibility.Analysis
