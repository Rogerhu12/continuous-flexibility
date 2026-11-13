import ContinuousFlexibility.Analysis.ActualNegativeReferenceInverseMaterialJets
import ContinuousFlexibility.Analysis.ActualNegativeReferencePotentialGerms
import ContinuousFlexibility.Analysis.RadialUnitDensityPotentialJets

/-!
# Actual negative reference potential jets at the original half sample

The stored physical height, stored scalar inverse and stored potential
are fixed throughout. Only numerical scales from their proven estimates
are combined. The full planar germ identifies the actual mixed jets;
positive angular orders vanish and the radial jets use the physical
unit-density flux formula on the same true half.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

private theorem negativePotential_profile_prefix
    {D : ReferenceData} (hD : RadialProfileGeometry D) (N : ℕ) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ q, q ≤ N → ∀ r ∈ Icc D.a D.b,
      |iteratedDeriv q D.w r| ≤ P := by
  classical
  have hb (q : Fin (N + 1)) : ∃ A : ℝ, ∀ r ∈ Icc D.a D.b,
      ‖iteratedDeriv q.val D.w r‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv q.val hD.2.2.1.1 (by simp)).continuousOn
  choose A hA using hb
  refine ⟨1 + ∑ q : Fin (N + 1), |A q|,
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro q hq r hr
  let j : Fin (N + 1) := ⟨q, by omega⟩
  have hj : |iteratedDeriv q D.w r| ≤ A j := by
    simpa only [Real.norm_eq_abs] using hA j r hr
  exact ((hj.trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun q : Fin (N + 1) => |A q|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j))).trans
      (le_add_of_nonneg_left zero_le_one)

/-- Every mixed derivative of the actual stored reference potential is
bounded at the original negative-half sample. The uniform optical lower
input is retained explicitly until supplied by the same construction. -/
theorem n04bActualTypedAtlas_reference_half_potential_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (hK₀ : 0 < K₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      ∀ p ∈ canonicalOpen S K k, ∀ a b : ℕ,
        |mixedDerivative a b (K.potential (C.referenceState, 0) k) p| ≤
          B (a + b) * (C0 * T.E0 (T.sample (K.cell k))) ^ (B (a + b)) := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨CH, hCH, hfloorH, hheight⟩ :=
    n04bActualTypedAtlas_reference_half_height_physical_power_material_jets
      hT hS hN hfield e hK₀
  obtain ⟨B1, hB1, hheight1⟩ := hheight 1
  obtain ⟨B3, hB3, hheight3⟩ := hheight 3
  obtain ⟨Cinv, hCinv, hfloorI, BI, hBI, hinverse⟩ :=
    n04bActualTypedAtlas_reference_half_inverse_material_jets hT hS hN hfield e hK₀
  let C0 : ℝ := CH + Cinv
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; linarith only [hCH, hCinv]
  have hCH0 : CH ≤ C0 := le_add_of_nonneg_right (zero_le_one.trans hCinv)
  have hCI0 : Cinv ≤ C0 := le_add_of_nonneg_left (zero_le_one.trans hCH)
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorH j).trans (mul_le_mul_of_nonneg_right hCH0
      ((hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1.le))
  have hper (N : ℕ) : ∃ B : ℝ, 1 ≤ B ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      ∀ ξ, ξ ∈ Ioo (K.left k) (K.right k) →
        let H := fun r : ℝ => K.height (C.referenceState, 0) k (r, 0)
        let χ := fun t : ℝ => (K.inverseChart (C.referenceState, 0) k (t, 0)).1
        |iteratedDeriv N (fun t => D.w (χ t) * H (χ t) ^ 3 *
          deriv (fun r => D.w r * deriv H r) (χ t)) ξ| ≤
            B * (C0 * T.E0 (T.sample (K.cell k))) ^ B := by
    obtain ⟨P, hP, hprofile⟩ := negativePotential_profile_prefix hD (N + 1)
    obtain ⟨CN, hCN, hpotential⟩ := radialUnitDensityPotential_finiteJet_envelope N
    let total : ℝ := ∑ q ∈ Finset.range (N + 3), (B1 q + B3 q + BI q)
    have htotal : 0 ≤ total := Finset.sum_nonneg fun q _ =>
      add_nonneg (add_nonneg (zero_le_one.trans (hB1 q))
        (zero_le_one.trans (hB3 q))) (zero_le_one.trans (hBI q))
    let A : ℝ := 1 + P + total
    have hA : 1 ≤ A := by dsimp only [A]; linarith only [hP, htotal]
    have hPA : P ≤ A := by dsimp only [A]; linarith only [htotal]
    have hprefix (q : ℕ) (hq : q ≤ N + 2) :
        B1 q ≤ A ∧ B3 q ≤ A ∧ BI q ≤ A := by
      have hs : B1 q + B3 q + BI q ≤ total :=
        Finset.single_le_sum (fun j _ =>
          add_nonneg (add_nonneg (zero_le_one.trans (hB1 j))
            (zero_le_one.trans (hB3 j))) (zero_le_one.trans (hBI j)))
          (Finset.mem_range.mpr (by omega))
      dsimp only [A]
      constructor
      · linarith only [hs, hP, hB3 q, hBI q]
      · constructor
        · linarith only [hs, hP, hB1 q, hBI q]
        · linarith only [hs, hP, hB1 q, hB3 q]
    let coefficient : ℝ := CN * A ^ (N + 4)
    let exponent : ℝ := A * ((N + 4 : ℕ) : ℝ)
    let B : ℝ := 1 + coefficient + exponent
    have hc : 0 ≤ coefficient := mul_nonneg (zero_le_one.trans hCN)
      (pow_nonneg (zero_le_one.trans hA) _)
    have he : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _)
    have hB : 1 ≤ B := by dsimp only [B]; linarith only [hc, he]
    have hcB : coefficient ≤ B := by dsimp only [B]; linarith only [he]
    have heB : exponent ≤ B := by dsimp only [B]; linarith only [hc]
    refine ⟨B, hB, ?_⟩
    intro k m side hk j hhost hoptical ξ hξ
    have hek : e.symm (.inl (m, side)) = k := by rw [← hk, e.symm_apply_apply]
    subst k
    let i := e.symm (.inl (m, side))
    have hi : e i = .inl (m, side) := e.apply_symm_apply _
    let H : ℝ → ℝ := fun r => K.height (C.referenceState, 0) i (r, 0)
    let χ : ℝ → ℝ := fun t => (K.inverseChart (C.referenceState, 0) i (t, 0)).1
    let I := Ioo (n04bNegativeLeft C cut (m, side))
      (n04bNegativeRight C cut (m, side))
    let J := Ioo (K.left i) (K.right i)
    have hgeometry := n04Coordinates_actual_reference_negative_scalar_inverse
      hT hS hN hfield e m side
    have hH : ContDiffOn ℝ ∞ H I := hgeometry.2.1
    have hχ : ContDiffOn ℝ ∞ χ J := hgeometry.2.2.1
    have hmap : MapsTo χ J I := hgeometry.2.2.2.1
    have hr : χ ξ ∈ I := hmap hξ
    have hwhole : χ ξ ∈ Ioo (C.left m) (C.right m) :=
      n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hr
    have hcomponent := n01Properties_negativeRadialComponent hN.1.1 m
    have hcore : χ ξ ∈ radialCore D :=
      ⟨hcomponent.1.trans hwhole.1, hwhole.2.trans hcomponent.2.2.1⟩
    let E : ℝ := T.E0 (T.sample (K.cell i))
    let W : ℝ := C0 * E
    let WH : ℝ := CH * E
    let WI : ℝ := Cinv * E
    have hE : 0 < E :=
      (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell i))).2.2.1
    have hW : 1 ≤ W := hfloor (K.cell i)
    have hWH : 1 ≤ WH := hfloorH (K.cell i)
    have hWI : 1 ≤ WI := hfloorI (K.cell i)
    have hWHW : WH ≤ W := mul_le_mul_of_nonneg_right hCH0 hE.le
    have hWIW : WI ≤ W := mul_le_mul_of_nonneg_right hCI0 hE.le
    let M : ℝ := A * W ^ A
    have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA
      (Real.one_le_rpow hW (zero_le_one.trans hA))
    have hpack {V a : ℝ} (hV : 0 ≤ V) (hVW : V ≤ W)
        (ha0 : 0 ≤ a) (ha : a ≤ A) : a * V ^ a ≤ M :=
      mul_le_mul ha ((Real.rpow_le_rpow hV hVW ha0).trans
        (Real.rpow_le_rpow_of_exponent_le hW ha))
        (Real.rpow_nonneg hV _) (zero_le_one.trans hA)
    have hwj (q : ℕ) (hq : q ≤ N + 1) :
        |iteratedDeriv q D.w (χ ξ)| ≤ M :=
      (hprofile q hq _ ⟨hcore.1.le, hcore.2.le⟩).trans (hPA.trans
        (le_mul_of_one_le_right (zero_le_one.trans hA)
          (Real.one_le_rpow hW (zero_le_one.trans hA))))
    have hHj (q : ℕ) (hq : q ≤ N + 2) : |iteratedDeriv q H (χ ξ)| ≤ M := by
      have hh : |iteratedDeriv q H (χ ξ)| ≤ B1 q * WH ^ (B1 q) := by
        simpa only [Real.rpow_one] using
          hheight1 i m side hi j hhost hoptical (χ ξ) hr 0 q
      exact hh.trans (hpack (zero_le_one.trans hWH) hWHW
        (zero_le_one.trans (hB1 q)) (hprefix q hq).1)
    have hH3j (q : ℕ) (hq : q ≤ N) :
        |iteratedDeriv q (fun r => H r ^ 3) (χ ξ)| ≤ M := by
      have hh : |iteratedDeriv q (fun r => H r ^ 3) (χ ξ)| ≤ B3 q * WH ^ (B3 q) := by
        simpa only [Real.rpow_ofNat] using
          hheight3 i m side hi j hhost hoptical (χ ξ) hr 0 q
      exact hh.trans (hpack (zero_le_one.trans hWH) hWHW
        (zero_le_one.trans (hB3 q)) (hprefix q (by omega)).2.1)
    have hχj (q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) : |iteratedDeriv q χ ξ| ≤ M := by
      have hiq : |iteratedDeriv q χ ξ| ≤ BI (q - 1) * WI ^ (BI (q - 1)) := by
        have hh := hinverse i m side hi j hhost hoptical ξ hξ (q - 1)
        simpa only [Nat.sub_add_cancel hq] using hh
      exact hiq.trans (hpack (zero_le_one.trans hWI) hWIW
        (zero_le_one.trans (hBI (q - 1))) (hprefix (q - 1) (by omega)).2.2)
    have hb := hpotential hM D.w H χ ξ hD.2.2.1.1.contDiffAt
      (hH.contDiffAt (isOpen_Ioo.mem_nhds hr))
      (hχ.contDiffAt (isOpen_Ioo.mem_nhds hξ)) hwj hHj hH3j hχj
    calc
      _ ≤ CN * M ^ (N + 4) := hb
      _ = coefficient * W ^ exponent := by
        dsimp only [M, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) A (N + 4)]
        ring
      _ ≤ coefficient * W ^ B := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW heB) hc
      _ ≤ B * W ^ B := mul_le_mul_of_nonneg_right hcB
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  choose B hB hbound using hper
  refine ⟨C0, hC0, hfloor, B, hB, ?_⟩
  intro k m side hk j hhost hoptical p hp a b
  have hek : e.symm (.inl (m, side)) = k := by rw [← hk, e.symm_apply_apply]
  subst k
  have hjet := (n04Coordinates_actual_reference_negative_potential_germ
    hT hS hN hfield e m side p hp).2 a b
  rw [hjet]
  by_cases hb : b = 0
  · subst b
    rw [if_pos rfl]
    simpa only [Nat.add_zero] using
      hbound a (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
        j hhost hoptical p.1 hp.1
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (zero_le_one.trans (hB (a + b)))
      (Real.rpow_nonneg (zero_le_one.trans (hfloor _)) _)

end ContinuousFlexibility.Analysis
