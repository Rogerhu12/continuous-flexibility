module

public import ContinuousFlexibility.Analysis.ActualNegativeReferenceHeightMaterialJets
public import ContinuousFlexibility.Analysis.ActualNegativeReferenceScalarInverse
public import ContinuousFlexibility.Analysis.RadialUnitDensityInverseJets

/-!
# Positive inverse-coordinate jets on the actual negative reference half

The inverse is the literal scalar slice of the stored inverse chart.
Height powers and reciprocal-profile jets are transferred to the exact
half sample before the finite inverse polynomial is used. The true
optical host remains distinct from the atlas sample cell. No zeroth
inverse-coordinate estimate or replacement inverse is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

/-- All positive ordinary derivatives of the actual scalar inverse have
a common material scale at the original half sample. The raw optical
lower bound is the same explicit input as in the actual height theorem. -/
theorem n04bActualTypedAtlas_reference_half_inverse_material_jets
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
      ∀ ξ, ξ ∈ Ioo (K.left k) (K.right k) → ∀ n : ℕ,
        |iteratedDeriv (n + 1)
          (fun t => (K.inverseChart (C.referenceState, 0) k (t, 0)).1) ξ| ≤
            B n * (C0 * T.E0 (T.sample (K.cell k))) ^ (B n) := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨C0, hC0, hfloor, hheight⟩ :=
    n04bActualTypedAtlas_reference_half_height_physical_power_material_jets
      hT hS hN hfield e hK₀
  obtain ⟨Bplus, hBplus, hplus⟩ := hheight 2
  obtain ⟨Bminus, hBminus, hminus⟩ := hheight (-2)
  have hprofileExists : ∃ P : ℝ, ∀ r ∈ Icc D.a D.b, ‖D.w r‖ ≤ P :=
    isCompact_Icc.exists_bound_of_continuousOn hD.2.2.1.1.continuous.continuousOn
  obtain ⟨P, hprofile⟩ := hprofileExists
  let P0 : ℝ := 1 + |P|
  have hP0 : 1 ≤ P0 := le_add_of_nonneg_right (abs_nonneg _)
  have hwvalue (r : ℝ) (hr : r ∈ Icc D.a D.b) : D.w r ≤ P0 := by
    have hb : |D.w r| ≤ P := by simpa only [Real.norm_eq_abs] using hprofile r hr
    exact ((le_abs_self _).trans hb).trans
      ((le_abs_self P).trans (le_add_of_nonneg_left zero_le_one))
  have hper (N : ℕ) : ∃ B : ℝ, 1 ≤ B ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      ∀ ξ, ξ ∈ Ioo (K.left k) (K.right k) →
        |iteratedDeriv (N + 1)
          (fun t => (K.inverseChart (C.referenceState, 0) k (t, 0)).1) ξ| ≤
            B * (C0 * T.E0 (T.sample (K.cell k))) ^ B := by
    obtain ⟨Ki, Pi, hKi, hPi, hiPoint⟩ :=
      material_inverseProfile_finite_point_jets hT hN.1.1.1.1 N
    obtain ⟨Ks, Ps, hKs, hPs, hiSample⟩ :=
      n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e 0 0 Pi hPi
    obtain ⟨CI, hCI, d, hinverse⟩ := radialUnitDensity_inverse_finiteJet_envelope N
    let sumMinus : ℝ := ∑ q ∈ Finset.range (N + 1), Bminus q
    have hsum : 0 ≤ sumMinus :=
      Finset.sum_nonneg fun q _ => zero_le_one.trans (hBminus q)
    have hKiKs : 0 < Ki * Ks := mul_pos hKi hKs
    let A : ℝ := 1 + Bplus 0 + P0 + Ki * Ks + Ps + sumMinus
    have hA : 1 ≤ A := by
      dsimp only [A]
      linarith only [hBplus 0, hP0, hKiKs, hPs, hsum]
    have hplusA : Bplus 0 ≤ A := by
      dsimp only [A]
      linarith only [hP0, hKiKs, hPs, hsum]
    have hprofileA : P0 ≤ A := by
      dsimp only [A]
      linarith only [hBplus 0, hKiKs, hPs, hsum]
    have hinvA : Ki * Ks ≤ A := by
      dsimp only [A]
      linarith only [hBplus 0, hP0, hPs, hsum]
    have hexpA : Ps ≤ A := by
      dsimp only [A]
      linarith only [hBplus 0, hP0, hKiKs, hsum]
    have hminusA (q : ℕ) (hq : q ≤ N) : Bminus q ≤ A := by
      have ht : Bminus q ≤ sumMinus :=
        Finset.single_le_sum (fun j _ => zero_le_one.trans (hBminus j))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
      dsimp only [A]
      linarith only [ht, hBplus 0, hP0, hKiKs, hPs]
    let coefficient : ℝ := CI * A ^ d
    let exponent : ℝ := A * (d : ℝ)
    let B : ℝ := 1 + coefficient + exponent
    have hc : 0 ≤ coefficient := mul_nonneg (zero_le_one.trans hCI)
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
    let Y : ℝ → ℝ := fun r => (K.chart (C.referenceState, 0) i (r, 0)).1
    let H : ℝ → ℝ := fun r => K.height (C.referenceState, 0) i (r, 0)
    let χ : ℝ → ℝ := fun t => (K.inverseChart (C.referenceState, 0) i (t, 0)).1
    let I := Ioo (n04bNegativeLeft C cut (m, side))
      (n04bNegativeRight C cut (m, side))
    let J := Ioo (K.left i) (K.right i)
    have hgeometry := n04Coordinates_actual_reference_negative_scalar_inverse
      hT hS hN hfield e m side
    have hY : ContDiffOn ℝ ∞ Y I := hgeometry.1
    have hH : ContDiffOn ℝ ∞ H I := hgeometry.2.1
    have hχ : ContDiffOn ℝ ∞ χ J := hgeometry.2.2.1
    have hmap : MapsTo χ J I := hgeometry.2.2.2.1
    have hright : ∀ x ∈ J, Y (χ x) = x := hgeometry.2.2.2.2.1
    have hunit : ∀ r ∈ I, 0 < H r ∧ H r ^ 2 * D.w r * |deriv Y r| = 1 :=
      hgeometry.2.2.2.2.2.2.1
    have hr : χ ξ ∈ I := hmap hξ
    have hrwhole : χ ξ ∈ Ioo (C.left m) (C.right m) :=
      n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hr
    have hcomponent := n01Properties_negativeRadialComponent hN.1.1 m
    have hcore : χ ξ ∈ radialCore D :=
      ⟨hcomponent.1.trans hrwhole.1, hrwhole.2.trans hcomponent.2.2.1⟩
    have hHpos : 0 < H (χ ξ) := (hunit _ hr).1
    have hwpos : 0 < D.w (χ ξ) := hD.2.2.2.2.1 _ hcore
    let E : ℝ := T.E0 (T.sample (K.cell i))
    let U : ℝ := C0 * E
    have hE : 0 < E :=
      (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell i))).2.2.1
    have hU : 1 ≤ U := hfloor (K.cell i)
    have hEU : E ≤ U := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
    let M : ℝ := A * U ^ A
    have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA
      (Real.one_le_rpow hU (zero_le_one.trans hA))
    have hpack {a p : ℝ} (ha : a ≤ A) (hp : p ≤ A) :
        a * U ^ p ≤ M :=
      mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hU hp)
        (Real.rpow_nonneg (zero_le_one.trans hU) _) (zero_le_one.trans hA)
    have hH2 : H (χ ξ) ^ 2 ≤ M := by
      have hh : |H (χ ξ) ^ 2| ≤ Bplus 0 * U ^ (Bplus 0) := by
        simpa only [iteratedDeriv_zero, Real.rpow_two] using
          hplus i m side hi j hhost hoptical (χ ξ) hr 0 0
      exact ((le_abs_self _).trans hh).trans (hpack hplusA hplusA)
    have hwM : D.w (χ ξ) ≤ M :=
      (hwvalue _ ⟨hcore.1.le, hcore.2.le⟩).trans (hprofileA.trans
        (le_mul_of_one_le_right (zero_le_one.trans hA)
          (Real.one_le_rpow hU (zero_le_one.trans hA))))
    have hHm (q : ℕ) (hq : q ≤ N) :
        |iteratedDeriv q (fun r => H r ^ (-2 : ℝ)) (χ ξ)| ≤ M :=
      (hminus i m side hi j hhost hoptical (χ ξ) hr 0 q).trans
        (hpack (hminusA q hq) (hminusA q hq))
    have hwi (q : ℕ) (hq : q ≤ N) :
        |iteratedDeriv q (fun r => (D.w r)⁻¹) (χ ξ)| ≤ M := by
      have hs : T.E0 (χ ξ) ^ Pi ≤ Ks * E ^ Ps := by
        simpa only [Real.rpow_zero, one_mul] using
          hiSample i m side hi (χ ξ) ⟨hrwhole.1.le, hrwhole.2.le⟩
      have hraw : |iteratedDeriv q (fun r => (D.w r)⁻¹) (χ ξ)| ≤
          (Ki * Ks) * E ^ Ps :=
        (hiPoint _ hcore q hq).trans
          ((mul_le_mul_of_nonneg_left hs hKi.le).trans_eq (by ring))
      exact hraw.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hE.le hEU hPs) hKiKs.le).trans (hpack hinvA hexpA))
    have hrightGerm : Y ∘ χ =ᶠ[𝓝 ξ] (id : ℝ → ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hξ] with x hx
      exact hright x hx
    have hunitGerm : ∀ᶠ r in 𝓝 (χ ξ), H r ^ 2 * D.w r * |deriv Y r| = 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with r hri
      exact (hunit r hri).2
    have hb := hinverse hM Y χ H D.w ξ
      (hY.contDiffAt (isOpen_Ioo.mem_nhds hr))
      (hχ.contDiffAt (isOpen_Ioo.mem_nhds hξ))
      (hH.contDiffAt (isOpen_Ioo.mem_nhds hr)) hD.2.2.1.1.contDiffAt
      hHpos hwpos hrightGerm hunitGerm hH2 hwM hHm hwi
    calc
      _ ≤ CI * M ^ d := hb
      _ = coefficient * U ^ exponent := by
        dsimp only [M, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hU) A d]
        ring
      _ ≤ coefficient * U ^ B := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU heB) hc
      _ ≤ B * U ^ B := mul_le_mul_of_nonneg_right hcB
        (Real.rpow_nonneg (zero_le_one.trans hU) _)
  choose B hB hbound using hper
  refine ⟨C0, hC0, hfloor, B, hB, ?_⟩
  intro k m side hk j hhost hoptical ξ hξ n
  exact hbound n k m side hk j hhost hoptical ξ hξ

end ContinuousFlexibility.Analysis
