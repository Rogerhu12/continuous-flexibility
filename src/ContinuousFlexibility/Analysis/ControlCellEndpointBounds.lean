import ContinuousFlexibility.Analysis.MaterialShiftedEnvelope
import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Endpoint bounds for control derivatives

The state mean and the control derivative are weighted at different cell
samples. The cell comparison places both samples at bounded distance from
the evaluation point in the endpoint coordinate. This gives a positive
power of the actual material height weight for their product.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX endpoint_log_pos materialH materialE0 material_bounded_shift_envelope)

private theorem endpointX_one_antitone {d e : ℝ} (hd : 0 < d) (hde : d ≤ e) :
    endpointX 1 e ≤ endpointX 1 d := by
  unfold endpointX
  apply Real.sqrt_le_sqrt
  have he := hd.trans_le hde
  rw [Real.log_div one_ne_zero he.ne', Real.log_div one_ne_zero hd.ne']
  simpa only [Real.log_one, zero_sub] using neg_le_neg (Real.log_le_log hd hde)

private theorem lt_endpointX_one_of_distance_lt {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hnear : d < Real.exp (-(L ^ 2))) : L < endpointX 1 d := by
  have hh := Real.log_lt_log hd hnear
  rw [Real.log_exp] at hh
  have hlog : L ^ 2 < Real.log (1 / d) := by
    rw [Real.log_div one_ne_zero hd.ne', Real.log_one, zero_sub]
    linarith only [hh]
  unfold endpointX
  calc
    L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hL).symm
    _ < Real.sqrt (Real.log (1 / d)) := Real.sqrt_lt_sqrt (sq_nonneg _) hlog

theorem abs_endpointX_scale_sub_le {d0 d : ℝ}
    (hd0 : 0 < d0) (hd : 0 < d) (hdd0 : d < d0) (hdd1 : d < 1) :
    |endpointX d0 d - endpointX 1 d| ≤ Real.sqrt |Real.log d0| := by
  let a := endpointX d0 d
  let b := endpointX 1 d
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = Real.log (d0 / d) := Real.sq_sqrt (endpoint_log_pos hd hdd0).le
  have hb2 : b ^ 2 = Real.log (1 / d) := Real.sq_sqrt (endpoint_log_pos hd hdd1).le
  have he : a ^ 2 - b ^ 2 = Real.log d0 := by
    rw [ha2, hb2, Real.log_div hd0.ne' hd.ne', Real.log_div one_ne_zero hd.ne', Real.log_one]
    ring
  have hsq : (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
    by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hb h 2))]
      nlinarith only [mul_nonneg hb (sub_nonneg.mpr h)]
    · have h' : a ≤ b := le_of_not_ge h
      rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ ha h' 2))]
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr h')]
  change |a - b| ≤ _
  calc
    |a - b| = Real.sqrt ((a - b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt |Real.log d0| := Real.sqrt_le_sqrt (he ▸ hsq)

/-- Nearby cell samples have uniformly bounded endpoint-coordinate displacement.
This is the geometric part of the material-weight comparison, shared by
estimates that retain the original height exponent. -/
theorem materialSample_endpoint_coordinate_comparison {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ d0 δ shift : ℝ, 0 < d0 ∧ 0 < δ ∧ 0 ≤ shift ∧
      ∀ (i j : ℕ) (r : ℝ), r ∈ Ioo D.a D.b → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B → endpointDistance D r < δ →
      let x := endpointX d0 (endpointDistance D r)
      let y := endpointX d0 (endpointDistance D (T.sample i))
      let z := endpointX d0 (endpointDistance D (T.sample j))
      2 * shift ≤ x ∧ |y - x| ≤ shift ∧ |z - x| ≤ shift ∧
        0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
        T.H (T.sample i) = materialH y ∧ T.E0 (T.sample j) = materialE0 z ∧
        T.H r = materialH x ∧ T.E0 r = materialE0 x := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _, _, _, _, hsamp, _, hcomp⟩ := hdata
  obtain ⟨d0, δ0, hd0, hδ0, hδbound, hleft, hright⟩ := hend
  obtain ⟨cellError, _, hcellError, _, hcmp⟩ := hcomp
  obtain ⟨_, hbounds⟩ := hRef
  let X1 (s : ℝ) := endpointX 1 (endpointDistance D s)
  let X (s : ℝ) := endpointX d0 (endpointDistance D s)
  let indexError := 2 * cellError + B
  let scaleError := Real.sqrt |Real.log d0|
  let shift := indexError + 2 * scaleError
  let η := min δ0 1
  let L := max (2 * shift + scaleError) (endpointX 1 η + indexError)
  let δ := min η (Real.exp (-(L ^ 2)))
  have hindexError : 0 ≤ indexError := add_nonneg (mul_nonneg (by norm_num) hcellError.le) hB
  have hscaleError : 0 ≤ scaleError := Real.sqrt_nonneg _
  have hshift : 0 ≤ shift := add_nonneg hindexError (mul_nonneg (by norm_num) hscaleError)
  have hL : 0 ≤ L := (add_nonneg (mul_nonneg (by norm_num) hshift) hscaleError).trans
    (le_max_left _ _)
  have hη : 0 < η := lt_min hδ0 zero_lt_one
  have hηδ : η ≤ δ0 := min_le_left _ _
  have hηd : η ≤ d0 := hηδ.trans (hδbound.trans_le (min_le_left _ _)).le
  have hη1 : η ≤ 1 := min_le_right _ _
  have hδ : 0 < δ := lt_min hη (Real.exp_pos _)
  have hdistance (s : ℝ) (hs : s ∈ Ioo D.a D.b) : 0 < endpointDistance D s :=
    lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)
  have hsampleCore (i : ℕ) : T.sample i ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hbounds.2.1 i
  have hX1 (i j : ℕ) (s : ℝ) (hs : s ∈ D.cells j)
      (hij : |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B) :
      |X1 (T.sample i) - X1 s| ≤ indexError := by
    have hi := abs_le.mp (hcmp i (T.sample i) (hsamp i)).1
    have hj := abs_le.mp (hcmp j s hs).1
    have hn := abs_le.mp hij
    apply abs_le.mpr
    constructor <;> dsimp only [X1, indexError] <;>
      linarith only [hi.1, hi.2, hj.1, hj.2, hn.1, hn.2]
  have hweights (s : ℝ) (hs : s ∈ Ioo D.a D.b) (hnear : endpointDistance D s < δ0) :
      T.H s = materialH (X s) ∧ T.E0 s = materialE0 (X s) := by
    unfold endpointDistance at hnear
    dsimp only [X, endpointDistance]
    by_cases hside : s - D.a ≤ D.b - s
    · rw [min_eq_left hside] at hnear ⊢
      have h := hleft s ⟨hs.1, by linarith only [hnear]⟩
      exact ⟨h.2.1, h.2.2.1⟩
    · have hside' : D.b - s ≤ s - D.a := le_of_not_ge hside
      rw [min_eq_right hside'] at hnear ⊢
      have h := hright s ⟨by linarith only [hnear], hs.2⟩
      exact ⟨h.2.1, h.2.2.1⟩
  have hscaleAt (s : ℝ) (hs : s ∈ Ioo D.a D.b) (hnear : endpointDistance D s < η) :
      |X s - X1 s| ≤ scaleError :=
    abs_endpointX_scale_sub_le hd0 (hdistance s hs) (hnear.trans_le hηd) (hnear.trans_le hη1)
  refine ⟨d0, δ, shift, hd0, hδ, hshift, fun i j r hr hrj hij hrnear => ?_⟩
  have hrη : endpointDistance D r < η := hrnear.trans_le (min_le_left _ _)
  have hlarge : L < X1 r := lt_endpointX_one_of_distance_lt (hdistance r hr) hL
    (hrnear.trans_le (min_le_right _ _))
  have hlargeS : endpointX 1 η + indexError < X1 r := (le_max_right _ _).trans_lt hlarge
  have hlargeR : 2 * shift + scaleError < X1 r := (le_max_left _ _).trans_lt hlarge
  have hiX1 := hX1 i j r hrj hij
  have hjX1 := hX1 j j r hrj (by simpa only [sub_self, abs_zero] using hB)
  have hsampleNear (k : ℕ) (hk : |X1 (T.sample k) - X1 r| ≤ indexError) :
      endpointDistance D (T.sample k) < η := by
    have hbig : endpointX 1 η < X1 (T.sample k) := by
      linarith only [hlargeS, (abs_le.mp hk).1]
    exact lt_of_not_ge fun hbad => (not_le_of_gt hbig) (endpointX_one_antitone hη hbad)
  have hscaleR := hscaleAt r hr hrη
  have hactualX : 2 * shift ≤ X r := by
    linarith only [hlargeR, (abs_le.mp hscaleR).1]
  have hactualClose (k : ℕ) (hknear : endpointDistance D (T.sample k) < η)
      (hkX1 : |X1 (T.sample k) - X1 r| ≤ indexError) :
      |X (T.sample k) - X r| ≤ shift := by
    have hk := abs_le.mp (hscaleAt (T.sample k) (hsampleCore k) hknear)
    have hr' := abs_le.mp hscaleR
    have hkr := abs_le.mp hkX1
    apply abs_le.mpr
    constructor <;> dsimp only [shift] <;>
      linarith only [hk.1, hk.2, hr'.1, hr'.2, hkr.1, hkr.2]
  have hiη := hsampleNear i hiX1
  have hjη := hsampleNear j hjX1
  have hiweights := hweights (T.sample i) (hsampleCore i) (hiη.trans_le hηδ)
  have hjweights := hweights (T.sample j) (hsampleCore j) (hjη.trans_le hηδ)
  have hrweights := hweights r hr (hrη.trans_le hηδ)
  exact ⟨hactualX, hactualClose i hiη hiX1, hactualClose j hjη hjX1,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    hiweights.1, hjweights.2, hrweights.1, hrweights.2⟩

/-- An actual material `H` weight and `E0` loss evaluated at two nearby cell indices. -/
theorem materialSample_endpoint_weight_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ (i j : ℕ) (r : ℝ),
      r ∈ Ioo D.a D.b → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B → endpointDistance D r < δ →
      T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ A ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨d0, δ, shift, _, hδ, hshift, hcoords⟩ :=
    materialSample_endpoint_coordinate_comparison hT hRef hB
  obtain ⟨K, hK, henv⟩ := material_bounded_shift_envelope hγ A hshift
  refine ⟨δ, K, hδ, hK, fun i j r hr hrj hij hrnear => ?_⟩
  obtain ⟨hx, hxy, hxz, _, _, hz, hHi, hEj, hHr, _⟩ :=
    hcoords i j r hr hrj hij hrnear
  rw [hHi, hEj, hHr]
  exact henv _ _ _ hx hxy hxz hz

/-- The actual state mean times each ordinary control jet decays in the endpoint collar. -/
theorem stateKappa_controlJet_endpoint_bound {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hN : N01Properties D T S C base loss ε)
    (hloc : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → r ∈ D.cells (C.cell m))
    (x : AnnularState S) (n : ℕ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      r ∈ Ioo (C.left m) (C.right m) → endpointDistance D r < δ →
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤
        K * T.H r ^ ((3 / 4 : ℝ) / 16) := by
  obtain ⟨_, _, _, _, hIndex, hJets, _⟩ := hN
  obtain ⟨B, hB, hindex⟩ := hIndex
  obtain ⟨Kc, hKc, hcontrol⟩ := hJets n
  obtain ⟨Kκ, hKκ, hκ⟩ := stateKappa_weight_bound_of_accumulatingProfile hS hT hRef x
  obtain ⟨δ, K, hδ, hK, henv⟩ :=
    materialSample_endpoint_weight_bound hT hRef (γ := (3 / 4 : ℝ)) (by norm_num) Kc hB.le
  have hnonneg : 0 ≤ Kκ * Kc := mul_nonneg hKκ hKc.le
  refine ⟨δ, (Kκ * Kc) * K, hδ, mul_nonneg hnonneg hK.le, fun m r hr hrI hrnear => ?_⟩
  have hi : |(D.cellIndex m : ℝ) - D.cellIndex (C.cell m)| ≤ B :=
    (abs_sub_comm _ _).trans_le (hindex m)
  have hw := henv m (C.cell m) r hr (hloc m r hrI) hi hrnear
  have hκ' : 0 ≤ Kκ * T.H (T.sample m) ^ (3 / 4 : ℝ) := (abs_nonneg _).trans (hκ m)
  rw [abs_mul]
  calc
    _ ≤ (Kκ * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        (Kc * T.E0 (T.sample (C.cell m)) ^ Kc) :=
      mul_le_mul (hκ m) (hcontrol m r hrI) (abs_nonneg _) hκ'
    _ = (Kκ * Kc) * (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ Kc) := by
      ring
    _ ≤ (Kκ * Kc) * (K * T.H r ^ ((3 / 4 : ℝ) / 16)) := mul_le_mul_of_nonneg_left hw hnonneg
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
