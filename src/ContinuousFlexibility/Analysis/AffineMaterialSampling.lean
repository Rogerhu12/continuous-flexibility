module

public import ContinuousFlexibility.Analysis.AffineMaterialData

/-!
# Sampling the material weights on the radial cells

The cell distance estimates bound the discrepancy between the cell index
and each endpoint variable used by the material weights. This preserves
the trace widths and controls both directions of the height-weight ratio.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX materialH materialE0 materialE0Exponent materialLogFactor
    materialIntervalXL materialIntervalXR materialIntervalTransition
    materialIntervalTransition_nonneg materialIntervalTransition_le_one
    materialIntervalLogBlend materialIntervalLogBlend_eq_left materialIntervalLogBlend_eq_right
    materialIntervalH materialIntervalLogH materialIntervalE0 materialIntervalLogE0)

private theorem endpointX_sub_index_le {L C d n : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hd : 0 < d) (hn : 0 ≤ n)
    (hlo : C⁻¹ * Real.exp (-((n + 1) ^ 2)) ≤ d)
    (hhi : d ≤ C * Real.exp (-(n ^ 2))) :
    |endpointX L d - n| ≤ 1 + Real.sqrt (|Real.log L| + |Real.log C|) := by
  have hlo' := Real.log_le_log (mul_pos (inv_pos.mpr hC) (Real.exp_pos _)) hlo
  have hhi' := Real.log_le_log hd hhi
  rw [Real.log_mul (inv_ne_zero hC.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp] at hlo'
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hhi'
  let S := |Real.log L| + |Real.log C|
  let R := Real.sqrt S
  let X := endpointX L d
  have hS : 0 ≤ S := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = S := Real.sq_sqrt hS
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hlow : n ^ 2 - S ≤ Real.log (L / d) := by
    rw [Real.log_div hL.ne' hd.ne']
    dsimp only [S]
    linarith only [hhi', neg_abs_le (Real.log L), le_abs_self (Real.log C)]
  have hupp : Real.log (L / d) ≤ (n + 1) ^ 2 + S := by
    rw [Real.log_div hL.ne' hd.ne']
    dsimp only [S]
    linarith only [hlo', le_abs_self (Real.log L), le_abs_self (Real.log C)]
  have hupper : X ≤ n + 1 + R := by
    change Real.sqrt (Real.log (L / d)) ≤ _
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith only [hn, hR], ?_⟩
    nlinarith only [hupp, hR2, mul_nonneg (add_nonneg hn zero_le_one) hR]
  have hlogSq : Real.log (L / d) ≤ X ^ 2 := by
    by_cases h : 0 ≤ Real.log (L / d)
    · exact (Real.sq_sqrt h).symm.le
    · exact (le_of_not_ge h).trans (sq_nonneg X)
  have hlower : n ≤ X + R := by
    apply (sq_le_sq₀ hn (add_nonneg hX hR)).mp
    nlinarith only [hlow, hlogSq, hR2, mul_nonneg hX hR]
  change |X - n| ≤ 1 + R
  exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper]⟩

/-- A bound on the active endpoint variables gives the same bound after the affine log blend. -/
private theorem affine_logBlend_le {D : ReferenceData} {C r U : ℝ} {n : ℕ}
    (hab : D.a < D.b) (hr : r ∈ Ioo D.a D.b) (hC : 0 < C)
    (hband : C⁻¹ * Real.exp (-(((n : ℝ) + 1) ^ 2)) ≤ endpointDistance D r ∧
      endpointDistance D r ≤ C * Real.exp (-((n : ℝ) ^ 2)))
    {f : ℝ → ℝ} (hf : ∀ x : ℝ, 0 ≤ x →
      |x - n| ≤ 1 + Real.sqrt (|Real.log (D.b - D.a)| + |Real.log (2 * C)|) → f x ≤ U) :
    materialIntervalLogBlend f (affineMaterialUnitCoordinate D r) ≤ U := by
  let L := D.b - D.a
  let dL := r - D.a
  let dR := D.b - r
  let d := endpointDistance D r
  let t := affineMaterialUnitCoordinate D r
  have hL : 0 < L := sub_pos.mpr hab
  have hdL : 0 < dL := sub_pos.mpr hr.1
  have hdR : 0 < dR := sub_pos.mpr hr.2
  have hd : 0 < d := lt_min hdL hdR
  have heq : dL + dR = L := by dsimp only [dL, dR, L]; ring
  have hCL : 0 < 2 * C := by positivity
  have hshift (s : ℝ) (hs₁ : d ≤ s) (hs₂ : s ≤ 2 * d) :
      f (endpointX L s) ≤ U := by
    have hi : (2 * C)⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hCL hC).mpr (by linarith only [hC])
    have hlo := (mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le).trans (hband.1.trans hs₁)
    have hhi : s ≤ (2 * C) * Real.exp (-((n : ℝ) ^ 2)) := by
      rw [mul_assoc]
      exact hs₂.trans (mul_le_mul_of_nonneg_left hband.2 (by norm_num))
    exact hf _ (Real.sqrt_nonneg _) (endpointX_sub_index_le hL hCL (hd.trans_le hs₁)
      (Nat.cast_nonneg n) hlo hhi)
  have hxL : materialIntervalXL t = endpointX L dL := by
    change Real.sqrt (Real.log (1 / (dL / L))) = _
    rw [one_div_div, endpointX]
  have hxR : materialIntervalXR t = endpointX L dR := by
    have hright : 1 - t = dR / L := by
      change 1 - dL / L = dR / L
      apply (eq_div_iff hL.ne').mpr
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hL.ne', ← heq, add_sub_cancel_left]
    change Real.sqrt (Real.log (1 / (1 - t))) = _
    rw [hright, one_div_div, endpointX]
  have hfL (hs : dL ≤ 2 * d) : f (materialIntervalXL t) ≤ U := by
    rw [hxL]
    exact hshift dL (min_le_left _ _) hs
  have hfR (hs : dR ≤ 2 * d) : f (materialIntervalXR t) ≤ U := by
    rw [hxR]
    exact hshift dR (min_le_right _ _) hs
  change materialIntervalLogBlend f t ≤ U
  by_cases hleft : t ≤ 1 / 3
  · have hleft' : dL ≤ (1 / 3 : ℝ) * L := (div_le_iff₀ hL).mp hleft
    have hside : dL ≤ dR := by linarith only [hleft', heq, hL]
    rw [materialIntervalLogBlend_eq_left f hleft]
    apply hfL
    change dL ≤ 2 * min dL dR
    rw [min_eq_left hside]
    linarith only [hdL]
  by_cases hright : 2 / 3 ≤ t
  · have hright' : (2 / 3 : ℝ) * L ≤ dL := (le_div_iff₀ hL).mp hright
    have hside : dR ≤ dL := by linarith only [hright', heq, hL]
    rw [materialIntervalLogBlend_eq_right f hright]
    apply hfR
    change dR ≤ 2 * min dL dR
    rw [min_eq_right hside]
    linarith only [hdR]
  have hleft' : (1 / 3 : ℝ) * L ≤ dL := (le_div_iff₀ hL).mp (le_of_not_ge hleft)
  have hright' : dL ≤ (2 / 3 : ℝ) * L := (div_le_iff₀ hL).mp (le_of_not_ge hright)
  have hcloseL : dL ≤ 2 * d := by
    change dL ≤ 2 * min dL dR
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min (by linarith only [hdL]) (by linarith only [hright', heq])
  have hcloseR : dR ≤ 2 * d := by
    change dR ≤ 2 * min dL dR
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min (by linarith only [hleft', heq]) (by linarith only [hdR])
  have hη := materialIntervalTransition_nonneg t
  have hη' := sub_nonneg.mpr (materialIntervalTransition_le_one t)
  calc
    materialIntervalLogBlend f t ≤ (1 - materialIntervalTransition t) * U +
        materialIntervalTransition t * U := add_le_add
      (mul_le_mul_of_nonneg_left (hfL hcloseL) hη') (mul_le_mul_of_nonneg_left (hfR hcloseR) hη)
    _ = U := by ring

private theorem le_affine_logBlend {D : ReferenceData} {C r U : ℝ} {n : ℕ}
    (hab : D.a < D.b) (hr : r ∈ Ioo D.a D.b) (hC : 0 < C)
    (hband : C⁻¹ * Real.exp (-(((n : ℝ) + 1) ^ 2)) ≤ endpointDistance D r ∧
      endpointDistance D r ≤ C * Real.exp (-((n : ℝ) ^ 2)))
    {f : ℝ → ℝ} (hf : ∀ x : ℝ, 0 ≤ x →
      |x - n| ≤ 1 + Real.sqrt (|Real.log (D.b - D.a)| + |Real.log (2 * C)|) → U ≤ f x) :
    U ≤ materialIntervalLogBlend f (affineMaterialUnitCoordinate D r) := by
  have hneg := affine_logBlend_le hab hr hC hband (f := fun x => -f x)
    (fun x hx hb => neg_le_neg (hf x hx hb))
  unfold materialIntervalLogBlend at hneg ⊢
  linarith only [hneg]

private theorem one_le_materialLogFactor {x : ℝ} (hx : 0 ≤ x) : 1 ≤ materialLogFactor x := by
  have h := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hx)
  simpa only [Real.log_exp, materialLogFactor] using h

private theorem materialLogFactor_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    materialLogFactor x ≤ materialLogFactor y :=
  Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx) (add_le_add_right hxy _)

private theorem one_le_materialE0Exponent {x : ℝ} (hx : 0 ≤ x) : 1 ≤ materialE0Exponent x :=
  le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx _)
    (zero_le_one.trans (one_le_materialLogFactor hx)))

theorem one_add_sq_le_materialE0Exponent {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 ≤ 2 * materialE0Exponent x := by
  by_cases hx' : 1 ≤ x
  · have hs : x ^ 2 ≤ x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast x 2]
      exact Real.rpow_le_rpow_of_exponent_le hx' (by norm_num)
    have ht : x ^ (5 / 2 : ℝ) ≤ x ^ (5 / 2 : ℝ) * materialLogFactor x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_materialLogFactor hx)
        (Real.rpow_nonneg hx (5 / 2 : ℝ))
    unfold materialE0Exponent
    linarith only [hs, ht, sq_nonneg x]
  · have hs : x ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ hx (le_of_not_ge hx') 2
    linarith only [hs, one_le_materialE0Exponent hx]

theorem exists_materialE0Exponent_bound_of_shift {B : ℝ} (hB : 0 ≤ B) :
    ∃ A : ℝ, 0 < A ∧ ∀ n x : ℝ, 0 ≤ n → 0 ≤ x → |x - n| ≤ B →
      n ^ (5 / 2 : ℝ) * materialLogFactor n ≤ A * materialE0Exponent x := by
  let M := B + 1
  let p : ℝ := 5 / 2
  let A := max (M ^ p * materialLogFactor M) (M ^ p * (Real.log M + 1))
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hB]
  have hM' : 0 < M := zero_lt_one.trans_le hM
  have hp : 0 ≤ p := by norm_num [p]
  have hA : 0 < A := (mul_pos (Real.rpow_pos_of_pos hM' p)
    (zero_lt_one.trans_le (one_le_materialLogFactor hM'.le))).trans_le (le_max_left _ _)
  refine ⟨A, hA, fun n x hn hx hs => ?_⟩
  have hle : n ≤ x + B := by linarith only [(abs_le.mp hs).1]
  change n ^ p * materialLogFactor n ≤ _
  by_cases hx' : 1 ≤ x
  · have hnM : n ≤ M * x := by
      dsimp only [M]
      nlinarith only [hle, mul_nonneg hB (sub_nonneg.mpr hx')]
    have hpow : n ^ p ≤ M ^ p * x ^ p := by
      rw [← Real.mul_rpow hM'.le hx]
      exact Real.rpow_le_rpow hn hnM hp
    have hexp : Real.exp 1 + n ≤ M * (Real.exp 1 + x) := by
      nlinarith only [hnM, mul_nonneg (sub_nonneg.mpr hM) (Real.exp_pos 1).le]
    have hlog := Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hn) hexp
    rw [Real.log_mul hM'.ne' (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx).ne'] at hlog
    change materialLogFactor n ≤ Real.log M + materialLogFactor x at hlog
    have hlog' : materialLogFactor n ≤ (Real.log M + 1) * materialLogFactor x := by
      nlinarith only [hlog, mul_nonneg (Real.log_nonneg hM)
        (sub_nonneg.mpr (one_le_materialLogFactor hx))]
    have hxterm : 0 ≤ x ^ p * materialLogFactor x :=
      mul_nonneg (Real.rpow_nonneg hx p) (zero_le_one.trans (one_le_materialLogFactor hx))
    calc
      n ^ p * materialLogFactor n ≤ (M ^ p * x ^ p) * ((Real.log M + 1) * materialLogFactor x) :=
        mul_le_mul hpow hlog' (zero_le_one.trans (one_le_materialLogFactor hn))
          (mul_nonneg (Real.rpow_nonneg hM'.le p) (Real.rpow_nonneg hx p))
      _ = (M ^ p * (Real.log M + 1)) * (x ^ p * materialLogFactor x) := by ring
      _ ≤ A * (x ^ p * materialLogFactor x) := mul_le_mul_of_nonneg_right (le_max_right _ _) hxterm
      _ ≤ A * materialE0Exponent x := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        change x ^ p * materialLogFactor x ≤ 1 + x ^ p * materialLogFactor x
        linarith
  · have hnM : n ≤ M := by
      dsimp only [M]
      linarith only [hle, le_of_not_ge hx']
    calc
      n ^ p * materialLogFactor n ≤ M ^ p * materialLogFactor M :=
        mul_le_mul (Real.rpow_le_rpow hn hnM hp) (materialLogFactor_mono_nonneg hn hnM)
          (zero_le_one.trans (one_le_materialLogFactor hn)) (Real.rpow_nonneg hM'.le p)
      _ ≤ A := le_max_left _ _
      _ ≤ A * materialE0Exponent x := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_materialE0Exponent hx) hA.le

theorem log_materialH_shift_bound {B n x : ℝ} (hB : 0 ≤ B)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hs : |x - n| ≤ B) :
    |Real.log (materialH x) - (-2 * n ^ 3 / 3)| ≤ 4 * B * (1 + B ^ 2) * (1 + n ^ 2) := by
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

/-- Comparison with the discrete profile uses the same cell index for both weights. -/
theorem affineMaterialData_cell_log_bounds {D : ReferenceData} {sample : ℕ → ℝ}
    (hRef : IsAccumulatingProfile D) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ m r, r ∈ D.cells m →
      1 ≤ Real.log ((affineMaterialData D sample).E0 r) ∧
      radialQ (D.cellIndex m) ≤ A * Real.log ((affineMaterialData D sample).E0 r) ∧
      |Real.log ((affineMaterialData D sample).H r) + radialS (D.cellIndex m)| ≤
        K * (1 + (D.cellIndex m : ℝ) ^ 2) := by
  obtain ⟨C, hBounds⟩ := hRef
  obtain ⟨hGeom, hPart, hC, _, _, _, hDist, _⟩ := hBounds
  let B := 1 + Real.sqrt (|Real.log (D.b - D.a)| + |Real.log (2 * C 0)|)
  let K := 4 * B * (1 + B ^ 2)
  have hB : 0 ≤ B := add_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hK : 0 ≤ K := by positivity
  obtain ⟨A, hA, hAprop⟩ := exists_materialE0Exponent_bound_of_shift hB
  refine ⟨A, K, hA.le, hK, fun m r hr => ?_⟩
  let n := D.cellIndex m
  let T := affineMaterialData D sample
  let t := affineMaterialUnitCoordinate D r
  let J := K * (1 + (n : ℝ) ^ 2)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hrCore : r ∈ Ioo D.a D.b := hPart.2.2.2.1 m hr
  have hband := hDist m r hr
  have hE : Real.log (T.E0 r) = materialIntervalLogBlend (fun x => Real.log (materialE0 x)) t :=
    Real.log_exp _
  have hH : Real.log (T.H r) = materialIntervalLogBlend (fun x => Real.log (materialH x)) t :=
    Real.log_exp _
  have hE0 : 1 ≤ Real.log (T.E0 r) := by
    rw [hE]
    exact le_affine_logBlend hGeom.2.1 hrCore (hC 0) hband (fun x hx _ => by
      rw [materialE0, Real.log_exp]
      exact one_le_materialE0Exponent hx)
  have hE1 : radialQ n ≤ A * Real.log (T.E0 r) := by
    have hpoint (x : ℝ) (hx : 0 ≤ x) (hs : |x - n| ≤ B) :
        radialQ n ≤ A * Real.log (materialE0 x) := by
      rw [materialE0, Real.log_exp]
      exact hAprop n x hn hx hs
    have hlow : radialQ n / A ≤ Real.log (T.E0 r) := by
      rw [hE]
      exact le_affine_logBlend hGeom.2.1 hrCore (hC 0) hband (fun x hx hs =>
        (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hpoint x hx hs))
    simpa only [mul_comm] using (div_le_iff₀ hA).mp hlow
  have hHpoint (x : ℝ) (hx : 0 ≤ x) (hs : |x - n| ≤ B) :
      |Real.log (materialH x) + radialS n| ≤ J := by
    have heq : Real.log (materialH x) + radialS n =
        Real.log (materialH x) - (-2 * (n : ℝ) ^ 3 / 3) := by
      unfold radialS
      ring
    rw [heq]
    exact log_materialH_shift_bound hB hn hx hs
  have hHlo : -radialS n - J ≤ Real.log (T.H r) := by
    rw [hH]
    exact le_affine_logBlend hGeom.2.1 hrCore (hC 0) hband (fun x hx hs => by
      linarith only [(abs_le.mp (hHpoint x hx hs)).1])
  have hHhi : Real.log (T.H r) ≤ -radialS n + J := by
    rw [hH]
    exact affine_logBlend_le hGeom.2.1 hrCore (hC 0) hband (fun x hx hs => by
      linarith only [(abs_le.mp (hHpoint x hx hs)).2])
  exact ⟨hE0, hE1, abs_le.mpr ⟨by linarith only [hHlo], by linarith only [hHhi]⟩⟩

/-- The centers from the actual trace scaffold give all three sampling clauses of `IsMaterialData`. -/
theorem exists_affineMaterialData_sampling {D : ReferenceData} (hRef : IsAccumulatingProfile D) :
    ∃ sample : ℕ → ℝ, let T := affineMaterialData D sample
      (∀ m, T.sample m ∈ D.cells m) ∧
      (∃ widths : ℕ → ℝ, ∃ K : ℝ, 0 < K ∧
        (∀ m, 0 < widths m ∧ K⁻¹ * T.E0 (T.sample m) ^ (-K) ≤ widths m ∧
          Icc (T.sample m - widths m) (T.sample m + widths m) ⊆ D.cells m) ∧
        Pairwise (fun m n : ℕ => Disjoint
          (Ioo (T.sample m - widths m) (T.sample m + widths m))
          (Ioo (T.sample n - widths n) (T.sample n + widths n)))) ∧
      (∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ m r, r ∈ D.cells m →
        |endpointX 1 (endpointDistance D r) - D.cellIndex m| ≤ C ∧
        (T.H (T.sample m) / T.H r) ≤ C * T.E0 r ^ A ∧
        (T.H r / T.H (T.sample m)) ≤ C * T.E0 r ^ A) := by
  have hData := hRef
  obtain ⟨C, hBounds⟩ := hData
  obtain ⟨hGeom, hPart, hC, _, _, _, hDist, _, _, _, _, _, hTrace⟩ := hBounds
  obtain ⟨sample, widths, K₀, hK₀, hW, hdisj⟩ := hTrace
  obtain ⟨A, J, hA, hJ, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hRef
  let T := affineMaterialData D sample
  have hcore (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) : r ∈ Ioo D.a D.b := hPart.2.2.2.1 m hr
  have hpos (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) : 0 < T.H r ∧ 0 < T.E0 r := by
    have hp := affineMaterialData_positive (sample := sample) hGeom.2.1 (hcore m r hr)
    exact ⟨hp.2.1, hp.2.2.1⟩
  let K := max K₀ (K₀ * A)
  have hK : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hsample (m : ℕ) : T.sample m ∈ D.cells m := (hW m).1
  refine ⟨sample, hsample, ⟨widths, K, hK, ?_, hdisj⟩, ?_⟩
  · intro m
    let s := T.sample m
    let n := D.cellIndex m
    have hEs : 0 < T.E0 s := (hpos m s (hsample m)).2
    have hEs1 : 1 ≤ T.E0 s := by
      apply (Real.log_le_log_iff zero_lt_one hEs).mp
      rw [Real.log_one]
      exact zero_le_one.trans (hlog m s (hsample m)).1
    have hrad : radialE n ≤ T.E0 s ^ A := by
      apply (Real.log_le_log_iff (Real.exp_pos (radialQ n)) (Real.rpow_pos_of_pos hEs A)).mp
      rw [Real.log_exp, Real.log_rpow hEs]
      exact (hlog m s (hsample m)).2.1
    have hpow : T.E0 s ^ (-K) ≤ radialE n ^ (-K₀) := by
      calc
        _ ≤ T.E0 s ^ (-(K₀ * A)) :=
          Real.rpow_le_rpow_of_exponent_le hEs1 (neg_le_neg (le_max_right _ _))
        _ = (T.E0 s ^ A) ^ (-K₀) := by
          rw [show -(K₀ * A) = A * (-K₀) by ring, Real.rpow_mul hEs.le]
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (radialQ n)) hrad (neg_nonpos.mpr hK₀.le)
    refine ⟨(hW m).2.1, ?_, (hW m).2.2.2⟩
    exact (mul_le_mul ((inv_le_inv₀ hK hK₀).mpr (le_max_left _ _)) hpow
      (Real.rpow_nonneg hEs.le _) (inv_nonneg.mpr hK₀.le)).trans (hW m).2.2.1
  · let B := 1 + Real.sqrt (|Real.log 1| + |Real.log (C 0)|)
    let P := (2 * J) * (2 * (1 + A))
    have hB : 1 ≤ B := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hP : 0 ≤ P := by positivity
    refine ⟨B, P, zero_lt_one.trans_le hB, hP, fun m r hr => ?_⟩
    let n := D.cellIndex m
    let s := T.sample m
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hd : 0 < endpointDistance D r :=
      lt_min (sub_pos.mpr (hcore m r hr).1) (sub_pos.mpr (hcore m r hr).2)
    have hBand := hDist m r hr
    have hCoord : |endpointX 1 (endpointDistance D r) - n| ≤ B :=
      endpointX_sub_index_le zero_lt_one (hC 0) hd hn hBand.1 hBand.2
    have ⟨hlogE, hQ, hHr⟩ := hlog m r hr
    have hHs := (hlog m s (hsample m)).2.2
    have hN2 : 1 + (n : ℝ) ^ 2 ≤ 2 * (1 + A) * Real.log (T.E0 r) := by
      have h := one_add_sq_le_materialE0Exponent hn
      change 1 + (n : ℝ) ^ 2 ≤ 2 * (1 + radialQ n) at h
      nlinarith only [h, hQ, hlogE]
    have htotal : 2 * (J * (1 + (n : ℝ) ^ 2)) ≤ P * Real.log (T.E0 r) := by
      calc
        _ = (2 * J) * (1 + (n : ℝ) ^ 2) := by ring
        _ ≤ (2 * J) * (2 * (1 + A) * Real.log (T.E0 r)) :=
          mul_le_mul_of_nonneg_left hN2 (by positivity)
        _ = _ := by unfold P; ring
    have hHrp := (hpos m r hr).1
    have hHsp := (hpos m s (hsample m)).1
    have hEp := (hpos m r hr).2
    have hEr := Real.rpow_pos_of_pos hEp P
    have hRatio₁ : T.H s / T.H r ≤ T.E0 r ^ P := by
      apply (Real.log_le_log_iff (div_pos hHsp hHrp) hEr).mp
      rw [Real.log_div hHsp.ne' hHrp.ne', Real.log_rpow hEp]
      linarith only [(abs_le.mp hHs).2, (abs_le.mp hHr).1, htotal]
    have hRatio₂ : T.H r / T.H s ≤ T.E0 r ^ P := by
      apply (Real.log_le_log_iff (div_pos hHrp hHsp) hEr).mp
      rw [Real.log_div hHrp.ne' hHsp.ne', Real.log_rpow hEp]
      linarith only [(abs_le.mp hHr).2, (abs_le.mp hHs).1, htotal]
    have hBmul : T.E0 r ^ P ≤ B * T.E0 r ^ P := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hB hEr.le
    exact ⟨hCoord, hRatio₁.trans hBmul, hRatio₂.trans hBmul⟩

end ContinuousFlexibility.Statements
