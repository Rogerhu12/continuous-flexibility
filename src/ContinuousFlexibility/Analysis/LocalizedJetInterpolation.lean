import ContinuousFlexibility.Analysis.TameInterpolationProducts

/-!
# Fixed-loss interpolation for a localized derivative slot

The low order and loss are chosen before the radius of the low-order
box. Angular and material orders enter only through their sum. This
allows the base-point box to be centered at any actual state later.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

private theorem seminorm_product_bound_on_larger_first_ball
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B a b H : ℕ) {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 1 ≤ κ)
    (hunit : ∀ x y : E, p B x ≤ 1 → p B y ≤ 1 →
      p a x * p b y ≤ C * (1 + p H x + p H y))
    (x y : E) (hx : p B x ≤ κ) (hy : p B y ≤ 1) :
    p a x * p b y ≤ κ * C * (1 + p H x + p H y) := by
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  let x' : E := κ⁻¹ • x
  have hscale (j : ℕ) : p j x' = κ⁻¹ * p j x := by
    dsimp only [x']
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκpos)]
  have hx' : p B x' ≤ 1 := by
    rw [hscale, inv_mul_eq_div]
    exact (div_le_one hκpos).mpr hx
  have hhigh : p H x' ≤ p H x := by
    rw [hscale, inv_mul_eq_div]
    exact (div_le_iff₀ hκpos).mpr
      (le_mul_of_one_le_right (apply_nonneg _ _) hκ)
  have heq : p a x * p b y = κ * (p a x' * p b y) := by
    rw [hscale]
    field_simp [hκpos.ne'] <;> ring
  calc
    _ = κ * (p a x' * p b y) := heq
    _ ≤ κ * (C * (1 + p H x' + p H y)) :=
      mul_le_mul_of_nonneg_left (hunit x' y hx' hy) hκpos.le
    _ ≤ κ * (C * (1 + p H x + p H y)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (le_refl 1) hhigh) (le_refl _)) hC) hκpos.le
    _ = _ := by ring

/-- A fixed angular-material budget gives affine growth in one high
seminorm on a low-order box. The chosen base and loss do not depend on
the size of that box or on the output order. -/
theorem hasInterpolation_localized_slot_growth_all
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase oldLoss extra : ℕ) :
    ∃ B L : ℕ, oldBase ≤ B ∧ ∀ n : ℕ, ∀ K : ℝ, 0 ≤ K →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ b c : ℕ, b + c ≤ s → ∀ (x : E) (v : Fin n → E) (w : E),
        p B x ≤ K → (∀ i, p B (v i) ≤ 1) → p B w ≤ 1 →
        ((1 + p (b + oldLoss) x + ∑ i : Fin n, p (b + oldLoss) (v i)) *
          p (oldBase + c + extra) w + p (b + oldLoss + c + extra) w) ≤
        C * (1 + p (s + L) x + ∑ i : Fin n, p (s + L) (v i) + p (s + L) w) := by
  classical
  obtain ⟨B, ℓ, hB, hinterp⟩ := hasInterpolation_mul_local_growth
    p p hp hp hI hI (oldBase + oldLoss + extra) oldBase 1 1 zero_le_one zero_le_one
  let L : ℕ := max ℓ (max (oldBase + extra) (oldLoss + extra))
  have hℓ : ℓ ≤ L := le_max_left _ _
  have hbase : oldBase + extra ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hloss : oldLoss + extra ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, L, hB, ?_⟩
  intro n K hK s hs
  obtain ⟨C₀, hC₀, hunit⟩ := hinterp s hs
  let κ : ℝ := max K 1
  let C₁ : ℝ := κ * C₀
  have hκ : 1 ≤ κ := le_max_right _ _
  have hC₁ : 0 ≤ C₁ := mul_nonneg (zero_le_one.trans hκ) hC₀
  refine ⟨2 + ((n : ℝ) + 1) * C₁, by positivity, ?_⟩
  intro b c hbc x v w hx hv hw
  let R : ℝ := 1 + p (s + L) x + ∑ i : Fin n, p (s + L) (v i) + p (s + L) w
  have hx0 : 0 ≤ p (s + L) x := apply_nonneg _ _
  have hw0 : 0 ≤ p (s + L) w := apply_nonneg _ _
  have hsum0 : 0 ≤ ∑ i : Fin n, p (s + L) (v i) :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hlast : p (s + L) w ≤ R := by dsimp only [R]; linarith only [hx0, hsum0]
  have hloww : p (oldBase + c + extra) w ≤ R :=
    (hp (by omega) w).trans hlast
  have hhighw : p (b + oldLoss + c + extra) w ≤ R :=
    (hp (by omega) w).trans hlast
  have hprod (y : E) (hy : p B y ≤ κ) :
      p (b + oldLoss) y * p (oldBase + c + extra) w ≤
        C₁ * (1 + p (s + ℓ) y + p (s + ℓ) w) :=
    seminorm_product_bound_on_larger_first_ball p B (b + oldLoss)
      (oldBase + c + extra) (s + ℓ) hC₀ hκ
      (hunit _ _ (by omega)) y w hy hw
  have hpx : p (b + oldLoss) x * p (oldBase + c + extra) w ≤ C₁ * R := by
    have hb := hprod x (hx.trans (le_max_left _ _))
    have hxh : p (s + ℓ) x ≤ p (s + L) x := hp (by omega) x
    have hwh : p (s + ℓ) w ≤ p (s + L) w := hp (by omega) w
    exact hb.trans (mul_le_mul_of_nonneg_left
      (by dsimp only [R]; linarith only [hxh, hwh, hsum0]) hC₁)
  have hpv (i : Fin n) :
      p (b + oldLoss) (v i) * p (oldBase + c + extra) w ≤ C₁ * R := by
    have hb := hprod (v i) ((hv i).trans hκ)
    have hvh : p (s + ℓ) (v i) ≤ p (s + L) (v i) := hp (by omega) (v i)
    have hwh : p (s + ℓ) w ≤ p (s + L) w := hp (by omega) w
    have hisum : p (s + L) (v i) ≤ ∑ j : Fin n, p (s + L) (v j) :=
      Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (by dsimp only [R]; linarith only [hvh, hwh, hisum, hx0]) hC₁)
  have hsum : (∑ i : Fin n, p (b + oldLoss) (v i) * p (oldBase + c + extra) w) ≤
      (n : ℝ) * (C₁ * R) := by
    calc
      _ ≤ ∑ _i : Fin n, C₁ * R := Finset.sum_le_sum (fun i _ => hpv i)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = p (oldBase + c + extra) w +
        p (b + oldLoss) x * p (oldBase + c + extra) w +
        (∑ i : Fin n, p (b + oldLoss) (v i) * p (oldBase + c + extra) w) +
        p (b + oldLoss + c + extra) w := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ R + C₁ * R + (n : ℝ) * (C₁ * R) + R :=
      add_le_add (add_le_add (add_le_add hloww hpx) hsum) hhighw
    _ = _ := by dsimp only [R]; ring

theorem hasInterpolation_localized_slot_growth
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase oldLoss extra n : ℕ) :
    ∃ B L : ℕ, oldBase ≤ B ∧ ∀ K : ℝ, 0 ≤ K →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ b c : ℕ, b + c ≤ s → ∀ (x : E) (v : Fin n → E) (w : E),
        p B x ≤ K → (∀ i, p B (v i) ≤ 1) → p B w ≤ 1 →
        ((1 + p (b + oldLoss) x + ∑ i : Fin n, p (b + oldLoss) (v i)) *
          p (oldBase + c + extra) w + p (b + oldLoss + c + extra) w) ≤
        C * (1 + p (s + L) x + ∑ i : Fin n, p (s + L) (v i) + p (s + L) w) := by
  obtain ⟨B, L, hB, h⟩ := hasInterpolation_localized_slot_growth_all p hp hI oldBase oldLoss extra
  exact ⟨B, L, hB, h n⟩

/-- The same fixed derivative budget controls the quadratic expression
which occurs when a localized direction is the actual base height.
Both input occurrences are controlled on one low-order box. -/
theorem hasInterpolation_quadratic_local_growth
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase oldLoss extra : ℕ) :
    ∃ B L : ℕ, oldBase ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ b c : ℕ, b + c ≤ s → ∀ x : E, p B x ≤ R →
        ((1 + p (b + oldLoss) x) * (1 + p (oldBase + c + extra) x) +
          (1 + p (b + oldLoss + c + extra) x)) ≤ C * (1 + p (s + L) x) := by
  obtain ⟨B, L, hB, hlocal⟩ :=
    hasInterpolation_localized_slot_growth p hp hI oldBase oldLoss extra 0
  refine ⟨B, L + oldLoss, hB, ?_⟩
  intro R hR s hs
  obtain ⟨I, hI0, hi⟩ := hlocal R hR s hs
  let κ : ℝ := max R 1
  have hκ : 1 ≤ κ := le_max_right _ _
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  refine ⟨2 + 2 * κ * I, by positivity, ?_⟩
  intro b c hbc x hx
  let w : E := κ⁻¹ • x
  have hscale (j : ℕ) : p j w = κ⁻¹ * p j x := by
    dsimp only [w]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκpos)]
  have hw : p B w ≤ 1 := by
    rw [hscale, inv_mul_eq_div]
    exact (div_le_one hκpos).mpr (hx.trans (le_max_left _ _))
  have h := hi b c hbc x Fin.elim0 w hx (fun i => Fin.elim0 i) hw
  simp only [Fin.sum_univ_zero, add_zero] at h
  have hwh : p (s + L) w ≤ p (s + L) x := by
    rw [hscale, inv_mul_eq_div]
    exact (div_le_iff₀ hκpos).mpr
      (le_mul_of_one_le_right (apply_nonneg _ _) hκ)
  have hhigh : p (s + L) x ≤ p (s + (L + oldLoss)) x := hp (by omega) x
  have ha : p (b + oldLoss) x ≤ p (s + (L + oldLoss)) x := hp (by omega) x
  have hx0 : 0 ≤ p (s + (L + oldLoss)) x := apply_nonneg _ _
  have hproduct : (1 + p (b + oldLoss) x) * p (oldBase + c + extra) x +
      p (b + oldLoss + c + extra) x ≤
      2 * κ * I * (1 + p (s + (L + oldLoss)) x) := by
    calc
      _ = κ * ((1 + p (b + oldLoss) x) * p (oldBase + c + extra) w +
          p (b + oldLoss + c + extra) w) := by
        rw [hscale, hscale]
        field_simp [hκpos.ne'] <;> ring
      _ ≤ κ * (I * (1 + p (s + L) x + p (s + L) w)) :=
        mul_le_mul_of_nonneg_left h hκpos.le
      _ ≤ κ * (I * (2 * (1 + p (s + (L + oldLoss)) x))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith only [hwh, hhigh]) hI0) hκpos.le
      _ = _ := by ring
  calc
    _ = 2 + p (b + oldLoss) x +
        ((1 + p (b + oldLoss) x) * p (oldBase + c + extra) x +
          p (b + oldLoss + c + extra) x) := by ring
    _ ≤ 2 * (1 + p (s + (L + oldLoss)) x) +
        2 * κ * I * (1 + p (s + (L + oldLoss)) x) :=
      add_le_add (by linarith only [ha, hx0]) hproduct
    _ = _ := by ring

end ContinuousFlexibility.Statements

