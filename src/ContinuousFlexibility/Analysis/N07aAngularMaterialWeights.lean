import ContinuousFlexibility.Analysis.SpacesTraceGeometry
import ContinuousFlexibility.Radial.R11bWeightEmbedding

/-!
# Arbitrary material data and the reference cell attenuation

These comparisons use the endpoint formulas and cell comparison in the
actual `IsMaterialData` contract. They do not specialize the candidate to
the particular affine construction used to prove W01.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff

private theorem n07a_endpointX_change_scale {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hd1 : d < 1) (hdd : d < d₀) :
    |endpointX d₀ d - endpointX 1 d| ≤ Real.sqrt |Real.log d₀| := by
  let x := endpointX d₀ d
  let y := endpointX 1 d
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = Real.log (d₀ / d) :=
    Real.sq_sqrt (endpoint_log_pos hd hdd).le
  have hy2 : y ^ 2 = Real.log (1 / d) :=
    Real.sq_sqrt (endpoint_log_pos hd hd1).le
  have hdiff : x ^ 2 - y ^ 2 = Real.log d₀ := by
    rw [hx2, hy2, Real.log_div hd₀.ne' hd.ne',
      Real.log_div one_ne_zero hd.ne', Real.log_one]
    ring
  have hsq : (x - y) ^ 2 ≤ |Real.log d₀| := by
    by_cases hxy : y ≤ x
    · nlinarith only [mul_nonneg hy (sub_nonneg.mpr hxy),
        le_abs_self (Real.log d₀), hdiff]
    · nlinarith only [mul_nonneg hx (sub_nonneg.mpr (le_of_not_ge hxy)),
        neg_abs_le (Real.log d₀), hdiff]
  exact abs_le_of_sq_le_sq (hsq.trans_eq (Real.sq_sqrt (abs_nonneg _)).symm)
    (Real.sqrt_nonneg _)

private theorem n07a_log_materialH_shift {B n x : ℝ} (hB : 0 ≤ B)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hs : |x - n| ≤ B) :
    |Real.log (materialH x) + (2 / 3 : ℝ) * n ^ 3| ≤
      (4 * B * (1 + B ^ 2)) * (1 + n ^ 2) := by
  have hx' : x ≤ n + B := by linarith only [(abs_le.mp hs).2]
  have hn' : n ≤ n + B := le_add_of_nonneg_right hB
  have hsq : x ^ 2 + x * n + n ^ 2 ≤ 3 * (n + B) ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hx hx' 2, pow_le_pow_left₀ hn hn' 2,
      mul_le_mul hx' hn' hn (add_nonneg hn hB)]
  have hsum : 0 ≤ x ^ 2 + x * n + n ^ 2 := by positivity
  have hsq' : (n + B) ^ 2 ≤ 2 * (1 + B ^ 2) * (1 + n ^ 2) := by
    nlinarith only [sq_nonneg (n - B), mul_nonneg (sq_nonneg B) (sq_nonneg n)]
  rw [materialH, Real.log_exp, show -2 * x ^ 3 / 3 + (2 / 3 : ℝ) * n ^ 3 =
    -(2 / 3 : ℝ) * ((x - n) * (x ^ 2 + x * n + n ^ 2)) by ring,
    abs_mul, abs_mul, abs_of_nonneg hsum, show |-(2 / 3 : ℝ)| = 2 / 3 by norm_num]
  calc
    _ ≤ (2 / 3 : ℝ) * (B * (3 * (n + B) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hs hsq hsum hB) (by norm_num)
    _ = (2 * B) * (n + B) ^ 2 := by ring
    _ ≤ (2 * B) * (2 * (1 + B ^ 2) * (1 + n ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq' (by positivity)
    _ = _ := by ring

/-- The logarithm of every admissible material height weight has the same
cubic cell attenuation, with a uniformly quadratic error. -/
theorem n07a_material_cell_logH {D : ReferenceData} {T : MaterialData}
    (hpart : RadialPartition D) (hT : IsMaterialData D T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m r, r ∈ D.cells m →
      |Real.log (T.H r) + radialS (D.cellIndex m)| ≤
        A * (1 + (D.cellIndex m : ℝ) ^ 2) := by
  obtain ⟨hsmooth, hpos, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, hcell⟩ := hT
  obtain ⟨d₀, δ, hd₀, hδ, hδlim, hleft, hright⟩ := hend
  obtain ⟨C, _, hC, _, hcell⟩ := hcell
  have hδ0 : δ < d₀ := hδlim.trans_le (min_le_left _ _)
  have hδhalf : δ < (D.b - D.a) / 2 := hδlim.trans_le (min_le_right _ _)
  let d : ℝ := min δ (1 / 2)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d < 1 := (min_le_right δ (1 / 2)).trans_lt (by norm_num)
  have hsub : Icc (D.a + d) (D.b - d) ⊆ Ioo D.a D.b := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hlog : ContinuousOn (fun r => Real.log (T.H r)) (Ioo D.a D.b) :=
    (hsmooth T.H (by simp)).continuousOn.log (fun r hr => (hpos r hr).2.1.ne')
  obtain ⟨Z, hZ⟩ := isCompact_Icc.bddAbove_image (hlog.abs.mono hsub)
  let B : ℝ := Real.sqrt |Real.log d₀| + C
  let E : ℝ := 4 * B * (1 + B ^ 2)
  let N : ℝ := Real.sqrt (Real.log (1 / d)) + C
  let Q : ℝ := max Z 0 + (2 / 3 : ℝ) * N ^ 3
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) hC.le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hN : 0 ≤ N := add_nonneg (Real.sqrt_nonneg _) hC.le
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨max E Q, hE.trans (le_max_left _ _), fun m r hr => ?_⟩
  have hrCore := hpart.2.2.2.1 m hr
  have hc := (hcell m r hr).1
  have hn : 0 ≤ (D.cellIndex m : ℝ) := Nat.cast_nonneg _
  have hendpoint (s : ℝ) (hs : 0 < s) (hsd : s < d)
      (hds : endpointDistance D r = s) (hH : T.H r = materialH (endpointX d₀ s)) :
      |Real.log (T.H r) + radialS (D.cellIndex m)| ≤
        max E Q * (1 + (D.cellIndex m : ℝ) ^ 2) := by
    have hscale := n07a_endpointX_change_scale hd₀ hs (hsd.trans hd1)
      (hsd.trans_le hdδ |>.trans hδ0)
    have hshift : |endpointX d₀ s - (D.cellIndex m : ℝ)| ≤ B := by
      calc
        _ ≤ |endpointX d₀ s - endpointX 1 s| +
            |endpointX 1 s - (D.cellIndex m : ℝ)| := abs_sub_le _ _ _
        _ ≤ Real.sqrt |Real.log d₀| + C := add_le_add hscale (by simpa only [hds] using hc)
    rw [hH]
    exact (n07a_log_materialH_shift hB hn (Real.sqrt_nonneg _) hshift).trans
      (mul_le_mul_of_nonneg_right (le_max_left E Q) (by positivity))
  by_cases hl : r < D.a + d
  · apply hendpoint (r - D.a) (sub_pos.mpr hrCore.1) (by linarith)
    · exact min_eq_left (by linarith [hδhalf])
    · exact (hleft r ⟨hrCore.1, by linarith⟩).2.1
  by_cases hh : D.b - d < r
  · apply hendpoint (D.b - r) (sub_pos.mpr hrCore.2) (by linarith)
    · exact min_eq_right (by linarith [hδhalf])
    · exact (hright r ⟨(sub_le_sub_left hdδ D.b).trans_lt hh, hrCore.2⟩).2.1
  have hrI : r ∈ Icc (D.a + d) (D.b - d) := ⟨le_of_not_gt hl, le_of_not_gt hh⟩
  have hdistance : d ≤ endpointDistance D r := le_min (by linarith [hrI.1])
    (by linarith [hrI.2])
  have hx : endpointX 1 (endpointDistance D r) ≤ Real.sqrt (Real.log (1 / d)) := by
    apply Real.sqrt_le_sqrt
    exact Real.log_le_log (one_div_pos.mpr (hd.trans_le hdistance))
      (one_div_le_one_div_of_le hd hdistance)
  have hnN : (D.cellIndex m : ℝ) ≤ N := by
    dsimp only [N]
    linarith only [hx, (abs_le.mp hc).1]
  have hbound : |Real.log (T.H r) + radialS (D.cellIndex m)| ≤ Q := by
    calc
      _ ≤ |Real.log (T.H r)| + |radialS (D.cellIndex m)| := abs_add_le _ _
      _ ≤ max Z 0 + (2 / 3 : ℝ) * N ^ 3 := add_le_add
        ((hZ ⟨r, hrI, rfl⟩).trans (le_max_left _ _)) (by
          rw [abs_of_nonneg (radialS_nonneg _)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hnN 3) (by norm_num))
  exact hbound.trans ((le_mul_of_one_le_right hQ (by nlinarith [sq_nonneg (D.cellIndex m : ℝ)])).trans
    (mul_le_mul_of_nonneg_right (le_max_right E Q) (by positivity)))

private theorem n07a_quadratic_le_cubic (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ n : ℕ, A * (1 + (n : ℝ) ^ 2) ≤ ε * radialS n + B := by
  let R : ℝ := 3 * A / (2 * ε)
  have hR : 0 ≤ R := div_nonneg (by positivity) (by positivity)
  refine ⟨A * (1 + R ^ 2), fun n => ?_⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  by_cases hsmall : (n : ℝ) ≤ R
  · have hsq := pow_le_pow_left₀ hn hsmall 2
    have he := mul_nonneg hε.le (radialS_nonneg n)
    have hp := mul_le_mul_of_nonneg_left hsq hA
    nlinarith only [hp, he]
  · have hl : A ≤ ε * (2 / 3 : ℝ) * (n : ℝ) := by
      have h := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp (le_of_not_ge hsmall)
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hl (sq_nonneg (n : ℝ))
    dsimp only [radialS]
    nlinarith [mul_nonneg hA (sq_nonneg R)]

/-- A strict attenuation margin absorbs the actual quadratic logarithmic
discrepancy. The statement concerns every original radial cell. -/
theorem n07a_material_reference_weight_bound {D : ReferenceData} {T : MaterialData}
    (hpart : RadialPartition D) (hT : IsMaterialData D T)
    {γ β : ℝ} (hβ : 0 ≤ β) (hγβ : γ < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      Real.exp (γ * radialS (D.cellIndex m)) * T.H r ^ β ≤ C := by
  obtain ⟨A, hA, hlog⟩ := n07a_material_cell_logH hpart hT
  obtain ⟨B, hB⟩ := n07a_quadratic_le_cubic (β * A) (β - γ)
    (mul_nonneg hβ hA) (sub_pos.mpr hγβ)
  refine ⟨Real.exp B, Real.exp_pos _, fun m r hr => ?_⟩
  have hH := (hT.2.1 r (hpart.2.2.2.1 m hr)).2.1
  rw [Real.rpow_def_of_pos hH, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left ((abs_le.mp (hlog m r hr)).2) hβ
  have hb := hB (D.cellIndex m)
  nlinarith only [hh, hb]

/-- Any fixed material power is harmless when a strict cubic attenuation
margin remains. No particular formula for the material data in the middle
of the annulus is used. -/
theorem n07a_material_reference_weight_with_M {D : ReferenceData} {T : MaterialData}
    (hpart : RadialPartition D) (hT : IsMaterialData D T)
    {γ β : ℝ} (hβ : 0 < β) (hγβ : γ < β) (q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      Real.exp (γ * radialS (D.cellIndex m)) * T.H r ^ β * T.M r ^ q ≤ C := by
  let β₀ : ℝ := (max γ 0 + β) / 2
  have hb0 : 0 < β₀ := by dsimp only [β₀]; linarith [le_max_right γ 0]
  have hb0β : β₀ < β := by
    dsimp only [β₀]
    have hmax : max γ 0 < β := max_lt hγβ hβ
    linarith
  have hγb0 : γ < β₀ := by dsimp only [β₀]; linarith [le_max_left γ 0]
  obtain ⟨A, hA, hweight⟩ := n07a_material_reference_weight_bound hpart hT hb0.le hγb0
  obtain ⟨B, hB, henvelope, _, _⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 q (β - β₀)
    (sub_pos.mpr hb0β)
  refine ⟨A * B, mul_pos hA hB, fun m r hr => ?_⟩
  have hcore := hpart.2.2.2.1 m hr
  have hH := (hT.2.1 r hcore).2.1
  have hM : 0 < T.M r := zero_lt_one.trans_le (hT.2.1 r hcore).2.2.2
  have he : T.H r ^ β = T.H r ^ β₀ * T.H r ^ (β - β₀) := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  rw [he]
  calc
    _ = (Real.exp (γ * radialS (D.cellIndex m)) * T.H r ^ β₀) *
        (T.H r ^ (β - β₀) * T.M r ^ q) := by ring
    _ ≤ A * B := mul_le_mul (hweight m r hr) (henvelope r hcore)
      (mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hM.le _)) hA.le

end ContinuousFlexibility.Statements
