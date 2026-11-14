module

public import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Reference coefficient jets in the actual material envelope

The discrete reference envelope is bounded by the endpoint envelope at the
same index. A bounded shift between that index and the actual endpoint
coordinate therefore transfers every nonnegative reference power to a
fixed power of `E0`. The compact middle meets only finitely many cells.

The hypothesis `E0 ≥ 1` is the property supplied by the explicit material
normalization; no coefficient or tame estimate is assumed. The resulting
comparison controls the actual reference profile and inverse-profile
radial jets, including their ordinary iterated-derivative formulation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The material coefficient envelope includes the discrete reference
envelope, with the same endpoint coordinate. -/
theorem radialE_le_materialE0 (n : ℕ) :
    radialE n ≤ materialE0 (n : ℝ) := by
  unfold radialE materialE0
  apply Real.exp_le_exp.mpr
  dsimp only [radialQ, materialE0Exponent, materialLogFactor]
  linarith

/-- A bounded index-coordinate discrepancy transfers each nonnegative
reference power to one fixed positive material exponent. -/
theorem radialE_rpow_le_materialE0_of_shift
    (α : ℝ) (hα : 0 ≤ α) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      |x - (n : ℝ)| ≤ B → radialE n ^ α ≤ materialE0 x ^ K := by
  obtain ⟨K, hK, hbound⟩ := materialE0_rpow_le_of_bounded_shift α hB
  refine ⟨K, hK, fun n x hx hxn => ?_⟩
  exact (Real.rpow_le_rpow (Real.exp_pos (radialQ n)).le
    (radialE_le_materialE0 n) hα).trans
    (hbound x (n : ℝ) hx (Nat.cast_nonneg n)
      (by simpa only [abs_sub_comm] using hxn))

/-- At either actual endpoint the cell index and the material coordinate
differ by a fixed amount, without changing any height exponent. -/
theorem radialE_cell_rpow_endpoint_le_E0
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (α : ℝ) (hα : 0 ≤ α) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ),
      r ∈ Ioo D.a D.b → r ∈ D.cells m → endpointDistance D r < δ →
        radialE (D.cellIndex m) ^ α ≤ T.E0 r ^ K := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hends, _, _, _, _, _, _, hcompare⟩ := hdata
  obtain ⟨d0, δ0, hd0, hδ0, _, hL, hR⟩ := hends
  obtain ⟨B₀, _, hB₀, _, hindex⟩ := hcompare
  let δ : ℝ := min δ0 (min d0 1)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hd0 zero_lt_one)
  have hδ₀ : δ ≤ δ0 := min_le_left _ _
  have hδd : δ ≤ d0 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₁ : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let B : ℝ := Real.sqrt |Real.log d0| + B₀
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) hB₀.le
  obtain ⟨K, hK, hbound⟩ := radialE_rpow_le_materialE0_of_shift α hα hB
  refine ⟨δ, K, hδ, hK, fun m r hr hrm hnear => ?_⟩
  let x : ℝ := endpointX d0 (endpointDistance D r)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hd : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hscale := abs_endpointX_scale_sub_le hd0 hd
    (hnear.trans_le hδd) (hnear.trans_le hδ₁)
  have hi := (hindex m r hrm).1
  have hclose : |x - (D.cellIndex m : ℝ)| ≤ B := by
    calc
      |x - (D.cellIndex m : ℝ)| =
          |(x - endpointX 1 (endpointDistance D r)) +
            (endpointX 1 (endpointDistance D r) - (D.cellIndex m : ℝ))| := by
        congr 1
        ring
      _ ≤ |x - endpointX 1 (endpointDistance D r)| +
          |endpointX 1 (endpointDistance D r) - (D.cellIndex m : ℝ)| := abs_add_le _ _
      _ ≤ Real.sqrt |Real.log d0| + B₀ := add_le_add hscale hi
      _ = B := rfl
  have hE : T.E0 r = materialE0 x := by
    have hnear₀ := hnear.trans_le hδ₀
    change min (r - D.a) (D.b - r) < δ0 at hnear₀
    dsimp only [x, endpointDistance]
    by_cases hside : r - D.a ≤ D.b - r
    · rw [min_eq_left hside] at hnear₀ ⊢
      exact (hL r ⟨hr.1, by linarith only [hnear₀]⟩).2.2.1
    · have hside' : D.b - r ≤ r - D.a := le_of_not_ge hside
      rw [min_eq_right hside'] at hnear₀ ⊢
      exact (hR r ⟨by linarith only [hnear₀], hr.2⟩).2.2.1
  rw [hE]
  exact hbound (D.cellIndex m) x hx hclose

/-- Every fixed nonnegative reference-envelope power is bounded by one
material-envelope power on every actual radial cell. -/
theorem radialE_cell_rpow_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (α : ℝ) (hα : 0 ≤ α) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      radialE (D.cellIndex m) ^ α ≤ C * T.E0 r ^ K := by
  classical
  obtain ⟨δ, K, hδ, hK, hnear⟩ := radialE_cell_rpow_endpoint_le_E0 hT α hα
  obtain ⟨_, hbounds⟩ := hRef
  have hpart : RadialPartition D := hbounds.2.1
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : IsCompact middle := isCompact_Icc
  have hmiddleCore : middle ⊆ Ioo D.a D.b :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfinite : {m : ℕ | (D.cells m ∩ middle).Nonempty}.Finite :=
    hbounds.2.2.2.2.2.1 middle hmiddle hmiddleCore
  let indices : Finset ℕ := hfinite.toFinset
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex m) ^ α
  have hW (m : ℕ) : 0 ≤ W m :=
    Real.rpow_nonneg (Real.exp_pos (radialQ (D.cellIndex m))).le α
  let C : ℝ := 1 + ∑ m ∈ indices, W m
  have hC₁ : 1 ≤ C := by
    dsimp only [C]
    linarith [Finset.sum_nonneg (fun m (_ : m ∈ indices) => hW m)]
  have hC : 0 < C := zero_lt_one.trans_le hC₁
  refine ⟨C, K, hC, hK, fun m r hr => ?_⟩
  have hrCore : r ∈ Ioo D.a D.b := hpart.2.2.2.1 m hr
  have hEpow : 1 ≤ T.E0 r ^ K := Real.one_le_rpow (hE r hrCore) hK.le
  by_cases hcollar : endpointDistance D r < δ
  · exact (hnear m r hrCore hr hcollar).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₁
        (zero_le_one.trans hEpow))
  · have hd : δ ≤ endpointDistance D r := le_of_not_gt hcollar
    have hrMiddle : r ∈ middle := by
      have hh := le_min_iff.mp hd
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have hm : m ∈ indices := hfinite.mem_toFinset.mpr ⟨r, hr, hrMiddle⟩
    have hsum : W m ≤ ∑ j ∈ indices, W j :=
      Finset.single_le_sum (fun j _ => hW j) hm
    calc
      radialE (D.cellIndex m) ^ α = W m := rfl
      _ ≤ ∑ j ∈ indices, W j := hsum
      _ ≤ C := by dsimp only [C]; linarith
      _ ≤ C * T.E0 r ^ K := le_mul_of_one_le_right hC.le hEpow

private theorem contDiff_reference_radialJet {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) : ContDiff ℝ ∞ (radialJet s f) := by
  induction s with
  | zero => exact hf
  | succ s ih => exact (contDiff_infty_iff_deriv.mp ih).2

/-- Reference profile jets are uniformly bounded on the closed physical
interval, hence also by a positive power of the normalized envelope. -/
theorem referenceProfile_radialJet_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (s : ℕ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      |radialJet s D.w r| ≤ C * T.E0 r ^ K := by
  obtain ⟨_, hbounds⟩ := hRef
  have hw : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
  have hc : Continuous (fun r => |radialJet s D.w r|) :=
    (contDiff_reference_radialJet hw s).continuous.abs
  have hcompact : IsCompact (Icc D.a D.b) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hc.continuousOn
  let C : ℝ := max 1 B
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C, 1, hC, zero_lt_one, fun m r hr => ?_⟩
  have hrCore : r ∈ Ioo D.a D.b := hbounds.2.1.2.2.2.1 m hr
  have hb : |radialJet s D.w r| ≤ B :=
    hB ⟨r, ⟨hrCore.1.le, hrCore.2.le⟩, rfl⟩
  have hbc : B ≤ C := le_max_right _ _
  simpa only [Real.rpow_one] using
    hb.trans (hbc.trans (le_mul_of_one_le_right hC.le (hE r hrCore)))

/-- The inverse-profile jet estimate follows from its genuine reference
cell bound and the reference-to-material envelope comparison. -/
theorem referenceInverse_radialJet_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (s : ℕ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      |radialJet s (fun r => (D.w r)⁻¹) r| ≤ C * T.E0 r ^ K := by
  have hdata := hRef
  obtain ⟨A, hbounds⟩ := hdata
  obtain ⟨_, _, hA, _, _, _, _, _, _, hinv, _⟩ := hbounds
  obtain ⟨C, K, hC, hK, hbound⟩ := radialE_cell_rpow_le_E0 hT hRef hE (A s) (hA s).le
  refine ⟨A s * C, K, mul_pos (hA s) hC, hK, fun m r hr => ?_⟩
  calc
    |radialJet s (fun r => (D.w r)⁻¹) r| ≤
        A s * radialE (D.cellIndex m) ^ (A s) := hinv m r hr s
    _ ≤ A s * (C * T.E0 r ^ K) :=
      mul_le_mul_of_nonneg_left (hbound m r hr) (hA s).le
    _ = (A s * C) * T.E0 r ^ K := (mul_assoc _ _ _).symm

private theorem radialJet_eq_iteratedDeriv_for_bounds (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => simp only [radialJet, iteratedDeriv_zero]
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

theorem referenceProfile_iteratedDeriv_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (s : ℕ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      |iteratedDeriv s D.w r| ≤ C * T.E0 r ^ K := by
  simpa only [radialJet_eq_iteratedDeriv_for_bounds] using
    referenceProfile_radialJet_le_E0 hRef hE s

theorem referenceInverse_iteratedDeriv_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (s : ℕ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      |iteratedDeriv s (fun r => (D.w r)⁻¹) r| ≤ C * T.E0 r ^ K := by
  simpa only [radialJet_eq_iteratedDeriv_for_bounds] using
    referenceInverse_radialJet_le_E0 hT hRef hE s

end ContinuousFlexibility.Statements
