import ContinuousFlexibility.Analysis.ControlCellEndpointBounds
import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Actual material heights in the natural radial weights

The cell comparison in IsMaterialData controls the endpoint coordinate, not
the number of cells at a fixed index.  We first compare the logarithm of the
actual height with the cubic discrete exponent.  Every strictly smaller
height exponent then absorbs any fixed natural material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis (endpointX materialH)
open ContinuousFlexibility.Radial (radialQ_nonneg)

private theorem n07b_log_materialH_shift_bound {B n x : ℝ} (hB : 0 ≤ B)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hs : |x - n| ≤ B) :
    |Real.log (materialH x) - (-2 * n ^ 3 / 3)| ≤
      4 * B * (1 + B ^ 2) * (1 + n ^ 2) := by
  have hx' : x ≤ n + B := by linarith only [(abs_le.mp hs).2]
  have hn' : n ≤ n + B := le_add_of_nonneg_right hB
  have hsq : x ^ 2 + x * n + n ^ 2 ≤ 3 * (n + B) ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hx hx' 2, pow_le_pow_left₀ hn hn' 2,
      mul_le_mul hx' hn' hn (add_nonneg hn hB)]
  have hsum : 0 ≤ x ^ 2 + x * n + n ^ 2 := by positivity
  have hsq' : (n + B) ^ 2 ≤ 2 * (1 + B ^ 2) * (1 + n ^ 2) := by
    nlinarith only [sq_nonneg (n - B), mul_nonneg (sq_nonneg B) (sq_nonneg n)]
  rw [materialH, Real.log_exp, show -2 * x ^ 3 / 3 - (-2 * n ^ 3 / 3) =
    -(2 / 3 : ℝ) * ((x - n) * (x ^ 2 + x * n + n ^ 2)) by ring,
    abs_mul, abs_mul, abs_of_nonneg hsum, show |-(2 / 3 : ℝ)| = 2 / 3 by norm_num]
  calc
    _ ≤ (2 / 3 : ℝ) * (B * (3 * (n + B) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hs hsq hsum hB) (by norm_num)
    _ = (2 * B) * (n + B) ^ 2 := by ring
    _ ≤ (2 * B) * (2 * (1 + B ^ 2) * (1 + n ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq' (by positivity)
    _ = _ := by ring

/-- The upper cubic comparison holds for every material model, including its
arbitrary smooth interpolation in the compact middle of the annulus. -/
theorem n07b_material_cell_logH_upper_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ D.cells m →
      Real.log (T.H r) + radialS (D.cellIndex m) ≤
        K * (1 + (D.cellIndex m : ℝ) ^ 2) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, hcomp⟩ := hdata
  obtain ⟨d0, δ0, hd0, hδ0, hδbound, hleft, hright⟩ := hend
  obtain ⟨E, _, hE, _, hcmp⟩ := hcomp
  obtain ⟨C, hbounds⟩ := hD
  obtain ⟨_, hpart, _, _, _, hfinite, _⟩ := hbounds
  let δ := min δ0 1
  let J := Icc (D.a + δ) (D.b - δ)
  have hδ : 0 < δ := lt_min hδ0 zero_lt_one
  have hJcore : J ⊆ Ioo D.a D.b := by
    intro r hr
    change D.a + δ ≤ r ∧ r ≤ D.b - δ at hr
    constructor <;> linarith only [hr.1, hr.2, hδ]
  have hHcont : ContinuousOn (fun r => Real.log (T.H r)) J :=
    ((hT.1 T.H (by simp)).continuousOn.mono hJcore).log
      (fun r hr => (hT.2.1 r (hJcore hr)).2.1.ne')
  obtain ⟨CH, hCH⟩ := (isCompact_Icc : IsCompact J).bddAbove_image hHcont
  have hcells : Set.Finite {m | (D.cells m ∩ J).Nonempty} :=
    hfinite J isCompact_Icc hJcore
  obtain ⟨CS, hCS⟩ :=
    (hcells.image (fun m => radialS (D.cellIndex m))).bddAbove
  let B := Real.sqrt |Real.log d0| + E
  let K0 := 4 * B * (1 + B ^ 2)
  let K := max K0 (max (CH + CS) 0)
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) hE.le
  have hK : 0 ≤ K :=
    (le_max_right (CH + CS) 0).trans (le_max_right K0 (max (CH + CS) 0))
  refine ⟨K, hK, fun m r hr => ?_⟩
  have hrCore : r ∈ Ioo D.a D.b := hpart.2.2.2.1 m hr
  by_cases hnear : endpointDistance D r < δ
  · have hd : 0 < endpointDistance D r :=
      lt_min (sub_pos.mpr hrCore.1) (sub_pos.mpr hrCore.2)
    have hd0' : endpointDistance D r < d0 :=
      (hnear.trans_le (min_le_left δ0 1)).trans
        (hδbound.trans_le (min_le_left d0 ((D.b - D.a) / 2)))
    have hd1 : endpointDistance D r < 1 := hnear.trans_le (min_le_right δ0 1)
    have hscale := abs_endpointX_scale_sub_le hd0 hd hd0' hd1
    have hclose :
        |endpointX d0 (endpointDistance D r) - (D.cellIndex m : ℝ)| ≤ B :=
      (abs_sub_le _ (endpointX 1 (endpointDistance D r)) _).trans
        (add_le_add hscale (hcmp m r hr).1)
    have hheight : T.H r = materialH (endpointX d0 (endpointDistance D r)) := by
      have hnear0 : endpointDistance D r < δ0 :=
        hnear.trans_le (min_le_left δ0 1)
      by_cases hside : r - D.a ≤ D.b - r
      · have he : endpointDistance D r = r - D.a := min_eq_left hside
        rw [he] at hnear0 ⊢
        exact (hleft r ⟨hrCore.1, by linarith only [hnear0]⟩).2.1
      · have he : endpointDistance D r = D.b - r :=
          min_eq_right (le_of_not_ge hside)
        rw [he] at hnear0 ⊢
        exact (hright r ⟨by linarith only [hnear0], hrCore.2⟩).2.1
    have hcubic := n07b_log_materialH_shift_bound hB
      (Nat.cast_nonneg (D.cellIndex m)) (Real.sqrt_nonneg _) hclose
    have hupper :
        Real.log (T.H r) + radialS (D.cellIndex m) ≤
          K0 * (1 + (D.cellIndex m : ℝ) ^ 2) := by
      have hcubic' :
          Real.log (materialH (endpointX d0 (endpointDistance D r))) -
              (-2 * (D.cellIndex m : ℝ) ^ 3 / 3) ≤
            K0 * (1 + (D.cellIndex m : ℝ) ^ 2) :=
        (abs_le.mp hcubic).2
      calc
        _ = Real.log (materialH (endpointX d0 (endpointDistance D r))) -
            (-2 * (D.cellIndex m : ℝ) ^ 3 / 3) := by
          rw [hheight]
          unfold radialS
          ring
        _ ≤ _ := hcubic'
    exact hupper.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))
  · have hd : δ ≤ endpointDistance D r := le_of_not_gt hnear
    have hl : δ ≤ r - D.a := hd.trans (min_le_left _ _)
    have hh : δ ≤ D.b - r := hd.trans (min_le_right _ _)
    have hrJ : r ∈ J := by
      constructor <;> linarith only [hl, hh]
    have hH : Real.log (T.H r) ≤ CH := hCH ⟨r, hrJ, rfl⟩
    have hS : radialS (D.cellIndex m) ≤ CS :=
      hCS ⟨m, ⟨r, hr, hrJ⟩, rfl⟩
    calc
      Real.log (T.H r) + radialS (D.cellIndex m) ≤ CH + CS := add_le_add hH hS
      _ ≤ K := (le_max_left (CH + CS) 0).trans (le_max_right _ _)
      _ ≤ K * (1 + (D.cellIndex m : ℝ) ^ 2) := by
        nlinarith only [mul_nonneg hK (sq_nonneg (D.cellIndex m : ℝ))]

/-- A strict height-exponent gap absorbs every fixed natural material weight.
The conclusion is uniform over all actual cells and all their points. -/
theorem n07b_material_cell_weight_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        T.H r ^ (2 * β) ≤ C := by
  obtain ⟨K, hK, hlog⟩ := n07b_material_cell_logH_upper_bound hD hT
  obtain ⟨C0, hbounds⟩ := hD
  obtain ⟨_, hpart, _, _, _, _, _, _, _, _, _, habsorb, _⟩ := hbounds
  let a := |A| + 1
  let b := 2 * β * K + 1
  let ε := 2 * (β - γ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨K0, hK0, hbound⟩ := habsorb a b ε ha hb hε
  refine ⟨K0 * Real.exp (2 * β * K), mul_pos hK0 (Real.exp_pos _),
    fun m r hr => ?_⟩
  let n := D.cellIndex m
  have hH : 0 < T.H r := (hT.2.1 r (hpart.2.2.2.1 m hr)).2.1
  have hab : a * radialQ n + b * (n : ℝ) ^ 2 ≤
      Real.log K0 + ε * radialS n := by
    have ht := hbound n
    rw [radialE, ← Real.exp_mul, ← Real.exp_add] at ht
    have he : K0 * Real.exp (ε * radialS n) =
        Real.exp (Real.log K0 + ε * radialS n) := by
      rw [Real.exp_add, Real.exp_log hK0]
    rw [he] at ht
    have hl := Real.exp_le_exp.mp ht
    simpa only [mul_comm] using hl
  have hA : A * radialQ n ≤ a * radialQ n :=
    mul_le_mul_of_nonneg_right
      ((le_abs_self A).trans (le_add_of_nonneg_right zero_le_one)) (radialQ_nonneg n)
  have hbK : 2 * β * K * (n : ℝ) ^ 2 ≤ b * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (by dsimp only [b]; linarith) (sq_nonneg _)
  have hHlog := mul_le_mul_of_nonneg_left (hlog m r hr) (show 0 ≤ 2 * β by positivity)
  have hexponent :
      A * radialQ n + 2 * γ * radialS n + Real.log (T.H r) * (2 * β) ≤
        Real.log K0 + 2 * β * K := by
    dsimp only [ε] at hab
    change 2 * β * (Real.log (T.H r) + radialS n) ≤
      2 * β * (K * (1 + (n : ℝ) ^ 2)) at hHlog
    nlinarith only [hab, hA, hbK, hHlog]
  rw [Real.rpow_def_of_pos hH, ← Real.exp_add]
  calc
    _ ≤ Real.exp (Real.log K0 + 2 * β * K) := Real.exp_le_exp.mpr hexponent
    _ = K0 * Real.exp (2 * β * K) := by rw [Real.exp_add, Real.exp_log hK0]

end ContinuousFlexibility.Statements
