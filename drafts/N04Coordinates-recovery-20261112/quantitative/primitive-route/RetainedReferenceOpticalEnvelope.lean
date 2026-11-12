import ContinuousFlexibility.Analysis.RetainedNegativeComponentIdentification
import ContinuousFlexibility.Analysis.ScaledMorseMaterialOpticalEnvelope
import ContinuousFlexibility.Analysis.CentralOpticalComponentLower
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels

/-!
# Uniform optical coefficients for the same retained reference

The actual left and right tail surgeries, their retained cell maps and
the central glued germ give the three estimates. Exact component
identification applies them to every negative component of this same
reference. A fixed lower normalization of the actual material weight
combines the two powers without assuming `E0 ≥ 1` or changing the host.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem rpow_raise_with_scaled_lower
    {x C p q : ℝ} (hx : 0 < x) (hC : 0 < C)
    (hCx : 1 ≤ C * x) (hq : 0 ≤ q) :
    x ^ p ≤ C ^ q * x ^ (p + q) := by
  have h := Real.rpow_le_rpow zero_le_one hCx hq
  rw [Real.one_rpow, Real.mul_rpow hC.le hx.le] at h
  calc
    x ^ p = x ^ p * 1 := (mul_one _).symm
    _ ≤ x ^ p * (C ^ q * x ^ q) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le p)
    _ = C ^ q * x ^ (p + q) := by rw [Real.rpow_add hx]; ring

/-- The inverse optical coefficient is bounded by one sampled material
power uniformly before the component, its host, and the physical point.
Every geometric input is a certificate retained by the actual `R11a`
construction of this same `Γ`; no optical estimate is an input. -/
theorem retainedReference_uniform_optical_envelope
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hstart : 100 ≤ S.chain.index)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ l h : ℝ, ∀ j : ℕ,
      NegativeRadialComponent Γ.reference l h → Ioo l h ⊆ Γ.reference.cells j →
      ∃ κ : ℝ, 0 < κ ∧ κ⁻¹ ≤ C * T.E0 (T.sample j) ^ A ∧
        ∀ r ∈ Ioo l h,
          κ * min (r - l) (h - r) ≤
            -deriv Γ.reference.w r / (r * Γ.reference.w r) := by
  let D := S.family S.sigma
  let G := P.toEntryPair hS hband
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hE : IsAccumulatingProfile Γ.reference := hΓ.2.1
  obtain ⟨e, N, hN, hlabels, hindex, hcells, hlocal, hleft, hright, hfibers, ha, hb⟩ :=
    hcoordinates
  have hindexLE (m : ℕ) : D.cellIndex m ≤ Γ.reference.cellIndex m := by
    change (S.family S.sigma).cellIndex m ≤ Γ.reference.cellIndex m
    rw [hlabels, hindex]
    exact Nat.le_max_left _ _
  have hleftCells (m : ℕ) (r : ℝ)
      (hr : r ∈ Ioo D.a (S.entry false S.chain.index)) (hrm : r ∈ D.cells m) :
      G.radiusL * r ∈ Γ.reference.cells m := by
    apply hcells m
    change e (G.radiusL * r) ∈ D.cells m
    rw [← hleft r hr.2.le, e.apply_symm_apply]
    exact hrm
  have hrightCells (m : ℕ) (r : ℝ)
      (hr : r ∈ Ioo (S.entry true S.chain.index) D.b) (hrm : r ∈ D.cells m) :
      G.radiusR * r ∈ Γ.reference.cells m := by
    apply hcells m
    change e (G.radiusR * r) ∈ D.cells m
    rw [← hright r hr.1.le, e.apply_symm_apply]
    exact hrm
  obtain ⟨CL, AL, hCL, hAL, hleftBound⟩ :=
    morseRealization_scaled_material_optical_envelope
      (E := Γ.reference) (l := D.a) (h := S.entry false S.chain.index)
      hreal hS.2.2.1 hstart hT hE G.radiusL_pos G.heightL_pos.ne'
      (fun r hr => by rw [hw]; exact (G.left_tail r hr).1) hleftCells hindexLE
  obtain ⟨CR, AR, hCR, hAR, hrightBound⟩ :=
    morseRealization_scaled_material_optical_envelope
      (E := Γ.reference) (l := S.entry true S.chain.index) (h := D.b)
      hreal hS.2.2.1 hstart hT hE
      (G.radiusL_pos.trans_le G.radius_order) G.heightR_pos.ne'
      (fun r hr => by rw [hw]; exact (G.right_tail r hr).1) hrightCells hindexLE
  obtain ⟨κC, hκC, hcentral⟩ := G.central_optical_component_lower hq
  obtain ⟨C₀, hC₀, hfloor⟩ := material_E0_uniform_scaled_lower hT hE
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  let A := AL + AR
  let C := max (κC⁻¹ * C₀ ^ A) (max (CL * C₀ ^ AR) (CR * C₀ ^ AL))
  have hA : 0 ≤ A := add_nonneg hAL hAR
  have hC : 0 < C :=
    (mul_pos (inv_pos.mpr hκC) (Real.rpow_pos_of_pos hC₀pos A)).trans_le (le_max_left _ _)
  have hsample (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hE hT j)).2.2.1
  have hsampleFloor (j : ℕ) : 1 ≤ C₀ * T.E0 (T.sample j) :=
    hfloor _ (materialSample_mem_interval hE hT j)
  have hleftPower (j : ℕ) : CL * T.E0 (T.sample j) ^ AL ≤ C * T.E0 (T.sample j) ^ A := by
    have hraise := rpow_raise_with_scaled_lower (p := AL)
      (hsample j) hC₀pos (hsampleFloor j) hAR
    calc
      _ ≤ CL * (C₀ ^ AR * T.E0 (T.sample j) ^ A) :=
        mul_le_mul_of_nonneg_left hraise hCL.le
      _ = (CL * C₀ ^ AR) * T.E0 (T.sample j) ^ A := by ring
      _ ≤ C * T.E0 (T.sample j) ^ A := mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (hsample j).le A)
  have hrightPower (j : ℕ) : CR * T.E0 (T.sample j) ^ AR ≤ C * T.E0 (T.sample j) ^ A := by
    have hraise : T.E0 (T.sample j) ^ AR ≤ C₀ ^ AL * T.E0 (T.sample j) ^ A := by
      simpa only [A, add_comm AR AL] using
        rpow_raise_with_scaled_lower (p := AR) (hsample j) hC₀pos (hsampleFloor j) hAL
    calc
      _ ≤ CR * (C₀ ^ AL * T.E0 (T.sample j) ^ A) :=
        mul_le_mul_of_nonneg_left hraise hCR.le
      _ = (CR * C₀ ^ AL) * T.E0 (T.sample j) ^ A := by ring
      _ ≤ C * T.E0 (T.sample j) ^ A := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (hsample j).le A)
  have hcentralPower (j : ℕ) : κC⁻¹ ≤ C * T.E0 (T.sample j) ^ A := by
    have hf := Real.rpow_le_rpow zero_le_one (hsampleFloor j) hA
    rw [Real.one_rpow, Real.mul_rpow hC₀pos.le (hsample j).le] at hf
    calc
      κC⁻¹ = κC⁻¹ * 1 := (mul_one _).symm
      _ ≤ κC⁻¹ * (C₀ ^ A * T.E0 (T.sample j) ^ A) :=
        mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hκC.le)
      _ = (κC⁻¹ * C₀ ^ A) * T.E0 (T.sample j) ^ A := by ring
      _ ≤ C * T.E0 (T.sample j) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hsample j).le A)
  refine ⟨C, A, hC, hA, ?_⟩
  intro l h j hcomponent hhost
  rcases retainedReference_negative_component_identification P hS hband hq hΓ hw
      hcoordinates hcomponent with hmiddle | htail
  · rcases hmiddle with ⟨rfl, rfl⟩
    refine ⟨κC, hκC, hcentralPower j, ?_⟩
    intro r hr
    simpa only [hw] using hcentral r hr
  · obtain ⟨side, n, hn, hl, hh, hclosed⟩ := htail
    cases side with
    | false =>
      rw [hl, hh] at hhost ⊢
      have hsub : Ioo
          (S.chain.radius false n (morseLeftTurn (morseChainA S.chain n) (morseChainB S.chain n)))
          (S.chain.radius false n (morseRightTurn (morseChainA S.chain n) (morseChainB S.chain n))) ⊆
            Ioo D.a (S.entry false S.chain.index) :=
        fun r hr => hclosed (Ioo_subset_Icc_self hr)
      obtain ⟨hκ, hbound, hlower⟩ := hleftBound false n hn j hsub hhost
      exact ⟨_, hκ, hbound.trans (hleftPower j), hlower⟩
    | true =>
      rw [hl, hh] at hhost ⊢
      have hsub : Ioo
          (S.chain.radius true n (morseLeftTurn (morseChainA S.chain n) (morseChainB S.chain n)))
          (S.chain.radius true n (morseRightTurn (morseChainA S.chain n) (morseChainB S.chain n))) ⊆
            Ioo (S.entry true S.chain.index) D.b :=
        fun r hr => hclosed (Ioo_subset_Icc_self hr)
      obtain ⟨hκ, hbound, hlower⟩ := hrightBound true n hn j hsub hhost
      exact ⟨_, hκ, hbound.trans (hrightPower j), hlower⟩

end ContinuousFlexibility.Radial
