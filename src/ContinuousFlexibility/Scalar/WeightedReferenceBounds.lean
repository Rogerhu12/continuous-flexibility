import ContinuousFlexibility.Analysis.ControlCellEndpointBounds

/-!
# Material weights dominate the reference inverse

The reference profile is controlled on the actual radial cells.  Their
endpoint coordinates differ from the material endpoint coordinate by a
bounded amount.  The cubic decay of `H` therefore absorbs every fixed cell
coefficient loss.  Local finiteness handles the remaining compact interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX materialH materialE0 materialE0Exponent materialLogFactor
    material_shifted_envelope materialH_pos)

theorem RadialPartition.exists_cell {D : ReferenceData} (hP : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : ∃ m, r ∈ D.cells m := by
  classical
  by_contra hn
  have hzero (m : ℕ) : D.localizer m r = 0 := by
    by_contra h
    exact hn ⟨m, hP.2.2.1 m h⟩
  have hsum := (hP.2.2.2.2.1 r hr).2
  simp only [hzero, tsum_zero] at hsum
  norm_num at hsum

/-- Both actual endpoint weights use one nonnegative coordinate, and the cell
index is at most twice that coordinate in a uniform endpoint collar. -/
theorem material_referenceCell_endpoint_coordinate {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m r,
      r ∈ Ioo D.a D.b → r ∈ D.cells m → endpointDistance D r < δ →
      ∃ x : ℝ, 0 ≤ x ∧ (D.cellIndex m : ℝ) ≤ 2 * x ∧
        T.H r = materialH x ∧ T.E0 r = materialE0 x := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, hcomp⟩ := hdata
  obtain ⟨d0, δ0, hd0, hδ0, hδbound, hleft, hright⟩ := hend
  obtain ⟨cellError, _, hcellError, _, hcmp⟩ := hcomp
  let scaleError : ℝ := Real.sqrt |Real.log d0|
  let shift : ℝ := cellError + scaleError
  let L : ℝ := 2 * shift + scaleError
  let δ : ℝ := min (min δ0 1) (Real.exp (-(L ^ 2)))
  have hscaleError : 0 ≤ scaleError := Real.sqrt_nonneg _
  have hshift : 0 ≤ shift := add_nonneg hcellError.le hscaleError
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (by norm_num) hshift) hscaleError
  have hδ : 0 < δ := lt_min (lt_min hδ0 zero_lt_one) (Real.exp_pos _)
  refine ⟨δ, hδ, fun m r hr hrm hnear => ?_⟩
  let d : ℝ := endpointDistance D r
  let x : ℝ := endpointX d0 d
  let x1 : ℝ := endpointX 1 d
  have hd : 0 < d := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hdδ0 : d < δ0 := hnear.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hd1 : d < 1 := hnear.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hdd0 : d < d0 := hdδ0.trans (hδbound.trans_le (min_le_left _ _))
  have hscale : |x - x1| ≤ scaleError := abs_endpointX_scale_sub_le hd0 hd hdd0 hd1
  have hlarge : L < x1 := lt_endpointX_one_of_distance_lt hd hL
    (hnear.trans_le (min_le_right _ _))
  have hx : 2 * shift ≤ x := by
    dsimp only [L] at hlarge
    linarith only [hlarge, (abs_le.mp hscale).1]
  have hclose : |(D.cellIndex m : ℝ) - x| ≤ shift := by
    have hc := abs_le.mp (hcmp m r hrm).1
    have hs := abs_le.mp hscale
    apply abs_le.mpr
    constructor <;> dsimp only [shift, x1, d] at * <;>
      linarith only [hc.1, hc.2, hs.1, hs.2]
  have hweights : T.H r = materialH x ∧ T.E0 r = materialE0 x := by
    dsimp only [x, d, endpointDistance]
    by_cases hside : r - D.a ≤ D.b - r
    · rw [min_eq_left hside]
      have hn : r - D.a < δ0 := by simpa only [d, endpointDistance, min_eq_left hside] using hdδ0
      have h := hleft r ⟨hr.1, by linarith only [hn]⟩
      exact ⟨h.2.1, h.2.2.1⟩
    · have hside' : D.b - r ≤ r - D.a := le_of_not_ge hside
      rw [min_eq_right hside']
      have hn : D.b - r < δ0 := by simpa only [d, endpointDistance, min_eq_right hside'] using hdδ0
      have h := hright r ⟨by linarith only [hn], hr.2⟩
      exact ⟨h.2.1, h.2.2.1⟩
  refine ⟨x, Real.sqrt_nonneg _, ?_, hweights⟩
  linarith only [hx, (abs_le.mp hclose).2]

/-- A reference cell coefficient is bounded after multiplication by any
positive power of the actual material height weight near either endpoint. -/
theorem material_referenceCell_endpoint_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ m r,
      r ∈ Ioo D.a D.b → r ∈ D.cells m → endpointDistance D r < δ →
      T.H r ^ γ * radialE (D.cellIndex m) ^ A ≤ K := by
  obtain ⟨δ, hδ, hcoord⟩ := material_referenceCell_endpoint_coordinate hT
  obtain ⟨K, hK, henv⟩ := material_shifted_envelope hγ A
  refine ⟨δ, K, hδ, hK, fun m r hr hrm hnear => ?_⟩
  obtain ⟨x, hx0, hn, hH, _⟩ := hcoord m r hr hrm hnear
  have hE : radialE (D.cellIndex m) ≤ materialE0 (D.cellIndex m) := by
    unfold radialE radialQ materialE0 materialE0Exponent materialLogFactor
    apply Real.exp_le_exp.mpr
    linarith
  have hErpow : radialE (D.cellIndex m) ^ A ≤ materialE0 (D.cellIndex m) ^ A :=
    Real.rpow_le_rpow (Real.exp_pos _).le hE hA
  have hHone : materialH x ^ (γ / 16) ≤ 1 := by
    rw [materialH, ← Real.exp_mul, Real.exp_le_one_iff]
    have : 0 ≤ x ^ 3 := pow_nonneg hx0 3
    have : 0 ≤ γ / 16 := div_nonneg hγ.le (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by positivity) this
  rw [hH]
  calc
    _ ≤ materialH x ^ γ * materialE0 (D.cellIndex m) ^ A :=
      mul_le_mul_of_nonneg_left hErpow (Real.rpow_pos_of_pos (materialH_pos x) γ).le
    _ ≤ K * materialH x ^ (γ / 16) := henv x x (D.cellIndex m) hx0
      (by linarith only [hx0]) (Nat.cast_nonneg _) hn
    _ ≤ K := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hHone hK.le

/-- Cellwise reference growth implies a global weighted bound.  No continuity
of the function is needed: the finitely many cells meeting a compact interior
interval supply its bound there. -/
theorem weighted_bound_of_referenceCell_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ A C : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    {f : ℝ → ℝ}
    (hf : ∀ m r, r ∈ D.cells m → |f r| ≤ C * radialE (D.cellIndex m) ^ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, T.H r ^ γ * |f r| ≤ K := by
  classical
  obtain ⟨B, hB⟩ := hD
  obtain ⟨δ, K, hδ, hK, hnear⟩ := material_referenceCell_endpoint_bound hT hγ hA
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hB.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ := (hfinite.image (fun m => C * radialE (D.cellIndex m) ^ A)).bddAbove
  have henv := hT.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨H, hH, hHbound, _⟩ := henv 0 γ hγ
  have hheight (r : ℝ) (hr : r ∈ Ioo D.a D.b) : T.H r ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHbound r hr
  refine ⟨max (C * K) (H * max R 0), le_max_of_le_left (mul_nonneg hC hK.le), ?_⟩
  intro r hr
  obtain ⟨m, hrm⟩ := hB.2.1.exists_cell hr
  have hp : 0 ≤ T.H r ^ γ := (Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ).le
  by_cases hn : endpointDistance D r < δ
  · apply (le_max_left _ _).trans'
    calc
      _ ≤ T.H r ^ γ * (C * radialE (D.cellIndex m) ^ A) :=
        mul_le_mul_of_nonneg_left (hf m r hrm) hp
      _ = C * (T.H r ^ γ * radialE (D.cellIndex m) ^ A) := by ring
      _ ≤ C * K := mul_le_mul_of_nonneg_left (hnear m r hr hrm hn) hC
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrmid : r ∈ middle := by
      exact ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hRm : C * radialE (D.cellIndex m) ^ A ≤ R :=
      hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩
    exact (mul_le_mul (hheight r hr) ((hf m r hrm).trans (hRm.trans (le_max_left _ _)))
      (abs_nonneg _) hH.le).trans (le_max_right _ _)

/-- Every fixed ordinary jet of the reciprocal reference profile is dominated
by every positive material height power, even after an arbitrary `M` loss. -/
theorem weighted_referenceInverseJet_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      T.H r ^ γ * T.M r ^ A * |radialJet n (fun t => (D.w t)⁻¹) r| ≤ K := by
  obtain ⟨B, hB⟩ := hD
  have hBn := hB.2.2.1 n
  have hjets := hB.2.2.2.2.2.2.2.2.2.1
  have hhalf : 0 < γ / 2 := div_pos hγ (by norm_num)
  obtain ⟨K, hK, hKbound⟩ := weighted_bound_of_referenceCell_bound ⟨B, hB⟩ hT hhalf
    hBn.le hBn.le (fun m r hr => hjets m r hr n)
  have henv := hT.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨L, hL, hLbound, _⟩ := henv A (γ / 2) hhalf
  refine ⟨L * K, mul_nonneg hL.le hK, fun r hr => ?_⟩
  have hp := (hT.2.1 r hr).2.1
  have hfactor : T.H r ^ γ = T.H r ^ (γ / 2) * T.H r ^ (γ / 2) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [hfactor]
  calc
    _ = (T.H r ^ (γ / 2) * T.M r ^ A) *
        (T.H r ^ (γ / 2) * |radialJet n (fun t => (D.w t)⁻¹) r|) := by ring
    _ ≤ L * K := mul_le_mul (hLbound r hr) (hKbound r hr)
      (mul_nonneg (Real.rpow_pos_of_pos hp _).le (abs_nonneg _)) hL.le

end ContinuousFlexibility.Statements
