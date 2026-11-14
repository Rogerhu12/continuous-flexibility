module

public import ContinuousFlexibility.Analysis.AffineMaterialSampling
public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Converting control bounds to the canonical sampled material weight

A linear change of the discrete physical index costs a fixed power of the
coefficient weight. The actual affine material sampling bounds then absorb
that power into the envelope used by the nonlinear statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real

/-- Multiplicative index rescaling for the actual coefficient exponent. -/
theorem n01a_radialQ_scale_le {L : ℝ} (hL : 1 ≤ L) {k n : ℕ}
    (hkn : (k : ℝ) ≤ L * n) :
    radialQ k ≤ (L ^ (5 / 2 : ℝ) * (1 + Real.log L)) * radialQ n := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogn : 1 ≤ Real.log (Real.exp 1 + n) := Radial.ssv_one_le_log hn0
  have hp : (k : ℝ) ^ (5 / 2 : ℝ) ≤ L ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      _ ≤ (L * n) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hk0 hkn (by norm_num)
      _ = _ := Real.mul_rpow hLpos.le hn0
  have hinside : Real.exp 1 + k ≤ L * (Real.exp 1 + n) := by
    have he := mul_le_mul_of_nonneg_right hL (Real.exp_pos 1).le
    nlinarith
  have hl : Real.log (Real.exp 1 + k) ≤
      (1 + Real.log L) * Real.log (Real.exp 1 + n) := by
    calc
      _ ≤ Real.log (L * (Real.exp 1 + n)) := Real.log_le_log (by positivity) hinside
      _ = Real.log L + Real.log (Real.exp 1 + n) :=
        Real.log_mul hLpos.ne' (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlogn hlogL]
  have hprod := mul_le_mul hp hl
    (zero_le_one.trans (Radial.ssv_one_le_log hk0))
    (mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hn0 _))
  calc
    radialQ k ≤ (L ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ)) *
        ((1 + Real.log L) * Real.log (Real.exp 1 + n)) := hprod
    _ = _ := by unfold radialQ; ring

/-- Linear index growth is bounded by a fixed multiple of `1 + radialQ`. -/
theorem n01a_radialQ_linear_bound (H : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ k n : ℕ, (k : ℝ) ≤ H * (1 + (n : ℝ)) →
      radialQ k ≤ K * (1 + radialQ n) := by
  let L : ℝ := 1 + |H|
  let T : ℝ := L ^ (5 / 2 : ℝ) * (1 + Real.log L)
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg H]
  have hT : 0 ≤ T := mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) _)
    (by linarith [Real.log_nonneg hL])
  obtain ⟨c, C, hshift⟩ := Radial.radialQ_shift_le 1
  let K : ℝ := 1 + |T * c| + |T * C|
  have hK : 0 < K := by dsimp [K]; positivity
  have hcK : T * c ≤ K := by
    dsimp [K]
    linarith [le_abs_self (T * c), abs_nonneg (T * C)]
  have hCK : T * C ≤ K := by
    dsimp [K]
    linarith [le_abs_self (T * C), abs_nonneg (T * c)]
  refine ⟨K, hK, fun k n hkn => ?_⟩
  have hHL : H ≤ L := by dsimp [L]; linarith [le_abs_self H]
  have hkn' : (k : ℝ) ≤ L * ((n + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ H * (1 + (n : ℝ)) := hkn
      _ ≤ L * (1 + (n : ℝ)) := mul_le_mul_of_nonneg_right hHL (by positivity)
      _ = _ := by push_cast; ring
  have hscale : radialQ k ≤ T * radialQ (n + 1) := n01a_radialQ_scale_le hL hkn'
  calc
    _ ≤ T * radialQ (n + 1) := hscale
    _ ≤ T * (c * radialQ n + C) := mul_le_mul_of_nonneg_left (hshift n) hT
    _ = (T * c) * radialQ n + T * C := by ring
    _ ≤ K * radialQ n + K :=
      add_le_add (mul_le_mul_of_nonneg_right hcK (Radial.radialQ_nonneg n)) hCK
    _ = _ := by ring

theorem n01a_host_radialQ_bound (index host : ℕ → ℕ) {H : ℝ} (hH : 0 ≤ H)
    (hhost : ∀ m, (host m : ℝ) ≤ H * (1 + (m : ℝ)))
    (hindex : ∀ m, m ≤ 2 * index m + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ m, radialQ (host m) ≤ K * (1 + radialQ (index m)) := by
  obtain ⟨K, hK, hb⟩ := n01a_radialQ_linear_bound (2 * H)
  refine ⟨K, hK, fun m => hb (host m) (index m) ?_⟩
  have hm : (m : ℝ) ≤ 2 * (index m : ℝ) + 1 := by exact_mod_cast hindex m
  have ht := mul_le_mul_of_nonneg_left (show 1 + (m : ℝ) ≤ 2 * (1 + (index m : ℝ)) by
    linarith) hH
  exact (hhost m).trans (by nlinarith only [ht])

/-- Any sampled envelope with the stated logarithmic lower bound absorbs
all fixed powers of the host-cell coefficient weight. -/
theorem n01a_radialE_host_power_le_material (index host : ℕ → ℕ) (E : ℕ → ℝ)
    {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hhost : ∀ m, (host m : ℝ) ≤ H * (1 + (m : ℝ)))
    (hindex : ∀ m, m ≤ 2 * index m + 1)
    (hE : ∀ m, 1 ≤ E m)
    (hlog : ∀ m, radialQ (index m) ≤ A * Real.log (E m))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, B * radialE (host m) ^ B ≤ C * E m ^ C := by
  obtain ⟨K, hK, hq⟩ := n01a_host_radialQ_bound index host hH hhost hindex
  let J : ℝ := B * K * A
  let M : ℝ := B * Real.exp (B * K)
  let C : ℝ := M + J + 1
  have hJ : 0 ≤ J := mul_nonneg (mul_nonneg hB hK.le) hA
  have hM : 0 ≤ M := mul_nonneg hB (Real.exp_pos _).le
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith
  have hJC : J ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun m => ?_⟩
  have hepos : 0 < E m := zero_lt_one.trans_le (hE m)
  have hexp : B * radialQ (host m) ≤ B * K + J * Real.log (E m) := by
    have h₁ := mul_le_mul_of_nonneg_left (hq m) hB
    have h₂ := mul_le_mul_of_nonneg_left (hlog m) (mul_nonneg hB hK.le)
    dsimp only [J]
    nlinarith only [h₁, h₂]
  calc
    B * radialE (host m) ^ B = B * Real.exp (B * radialQ (host m)) := by
      rw [radialE, ← Real.exp_mul]
      congr 2
      ring
    _ ≤ B * Real.exp (B * K + J * Real.log (E m)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB
    _ = M * E m ^ J := by
      rw [Real.exp_add, Real.rpow_def_of_pos hepos]
      dsimp only [M]
      rw [mul_comm J (Real.log (E m))]
      ring
    _ ≤ C * E m ^ C := mul_le_mul hMC
      (Real.rpow_le_rpow_of_exponent_le (hE m) hJC)
      (Real.rpow_nonneg hepos.le _) hC.le

theorem n01a_control_jets_material_bound (index host : ℕ → ℕ) (E : ℕ → ℝ)
    {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hhost : ∀ m, (host m : ℝ) ≤ H * (1 + (m : ℝ)))
    (hindex : ∀ m, m ≤ 2 * index m + 1)
    (hE : ∀ m, 1 ≤ E m) (hlog : ∀ m, radialQ (index m) ≤ A * Real.log (E m))
    (χ : ℕ → ℝ → ℝ) (J : ℕ → Set ℝ)
    (hjets : ∀ s, ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ J m →
      |iteratedDeriv s (χ m) r| ≤ B * radialE (host m) ^ B) :
    ∀ s, ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ J m →
      |iteratedDeriv s (χ m) r| ≤ C * E m ^ C := by
  intro s
  obtain ⟨B, hB, hb⟩ := hjets s
  obtain ⟨C, hC, hc⟩ := n01a_radialE_host_power_le_material
    index host E hH hA hhost hindex hE hlog B hB.le
  exact ⟨C, hC, fun m r hr => (hb m r hr).trans (hc m)⟩

/-- The canonical affine material data satisfy the hypotheses of the
abstract sequence conversion at every actual selected sample point. -/
theorem n01a_control_jets_affineMaterialData {D : ReferenceData} {sample : ℕ → ℝ}
    (hRef : IsAccumulatingProfile D) (hsample : ∀ m, sample m ∈ D.cells m)
    (host : ℕ → ℕ) {H : ℝ} (hH : 0 ≤ H)
    (hhost : ∀ m, (host m : ℝ) ≤ H * (1 + (m : ℝ)))
    (hindex : ∀ m, m ≤ 2 * D.cellIndex m + 1)
    (χ : ℕ → ℝ → ℝ) (J : ℕ → Set ℝ)
    (hjets : ∀ s, ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ J m →
      |iteratedDeriv s (χ m) r| ≤ B * radialE (host m) ^ B) :
    ∀ s, ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ J m →
      |iteratedDeriv s (χ m) r| ≤
        C * (affineMaterialData D sample).E0 ((affineMaterialData D sample).sample m) ^ C := by
  obtain ⟨A, K, hA, _, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hRef
  obtain ⟨Q, hQ⟩ := hRef
  have hab : D.a < D.b := hQ.1.2.1
  have hpart : RadialPartition D := hQ.2.1
  let E : ℕ → ℝ := fun m => (affineMaterialData D sample).E0 (sample m)
  have hE (m : ℕ) : 1 ≤ E m := by
    have hp : 0 < E m :=
      (affineMaterialData_positive (sample := sample) hab
        (hpart.2.2.2.1 m (hsample m))).2.2.1
    have hl : 0 ≤ Real.log (E m) := zero_le_one.trans (hlog m (sample m) (hsample m)).1
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_zero, Real.exp_log hp] using he
  exact n01a_control_jets_material_bound D.cellIndex host E hH hA hhost hindex hE
    (fun m => (hlog m (sample m) (hsample m)).2.1) χ J hjets

end ContinuousFlexibility.Statements
