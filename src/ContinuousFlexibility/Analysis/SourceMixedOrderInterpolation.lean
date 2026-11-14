module

public import ContinuousFlexibility.Analysis.TameInterpolationProducts
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization
public import ContinuousFlexibility.Analysis.TameLocalCalculus
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Fixed-loss interpolation for coefficient jets times a height factor

The common low order and loss are chosen before the sizes of the low
balls. A coefficient one-high estimate and its complementary height
order then have affine growth in one common high grading. Unit bounds
are used only on directions, before multilinear normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

private theorem seminorm_product_bound_on_larger_balls
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (B a b H : ℕ) {C κp κq : ℝ} (hC : 0 ≤ C) (hκp : 1 ≤ κp) (hκq : 1 ≤ κq)
    (hunit : ∀ x y, p B x ≤ 1 → q B y ≤ 1 →
      p a x * q b y ≤ C * (1 + p H x + q H y))
    (x : E) (y : F) (hx : p B x ≤ κp) (hy : q B y ≤ κq) :
    p a x * q b y ≤ (κp * κq * C) * (1 + p H x + q H y) := by
  have hκp0 : 0 < κp := zero_lt_one.trans_le hκp
  have hκq0 : 0 < κq := zero_lt_one.trans_le hκq
  let x' : E := κp⁻¹ • x
  let y' : F := κq⁻¹ • y
  have hpx (j : ℕ) : p j x' = κp⁻¹ * p j x := by
    dsimp only [x']
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκp0)]
  have hqy (j : ℕ) : q j y' = κq⁻¹ * q j y := by
    dsimp only [y']
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκq0)]
  have hx' : p B x' ≤ 1 := by
    rw [hpx, inv_mul_eq_div]
    exact (div_le_one hκp0).mpr hx
  have hy' : q B y' ≤ 1 := by
    rw [hqy, inv_mul_eq_div]
    exact (div_le_one hκq0).mpr hy
  have hxh : p H x' ≤ p H x := by
    rw [hpx, inv_mul_eq_div]
    exact (div_le_iff₀ hκp0).mpr (le_mul_of_one_le_right (apply_nonneg _ _) hκp)
  have hyh : q H y' ≤ q H y := by
    rw [hqy, inv_mul_eq_div]
    exact (div_le_iff₀ hκq0).mpr (le_mul_of_one_le_right (apply_nonneg _ _) hκq)
  have hscale : p a x * q b y = (κp * κq) * (p a x' * q b y') := by
    rw [hpx, hqy]
    calc
      _ = (κp * κp⁻¹) * (κq * κq⁻¹) * (p a x * q b y) := by
        rw [mul_inv_cancel₀ hκp0.ne', mul_inv_cancel₀ hκq0.ne', one_mul, one_mul]
      _ = _ := by ring
  calc
    _ = (κp * κq) * (p a x' * q b y') := hscale
    _ ≤ (κp * κq) * (C * (1 + p H x' + q H y')) :=
      mul_le_mul_of_nonneg_left (hunit x' y' hx' hy') (mul_nonneg hκp0.le hκq0.le)
    _ ≤ (κp * κq) * (C * (1 + p H x + q H y)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith only [hxh, hyh]) hC)
        (mul_nonneg hκp0.le hκq0.le)
    _ = _ := by ring

/-- The base and the final loss are independent of the low-ball radii,
the number of directions, and the output order. -/
theorem hasInterpolation_oneHigh_height_local_growth
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (oldBase oldLoss offset requestedBase : ℕ) :
    ∃ B L : ℕ, max requestedBase oldBase ≤ B ∧
      ∀ n : ℕ, ∀ Kp Kq : ℝ, 0 ≤ Kp → 0 ≤ Kq →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ a c : ℕ, a + c ≤ s + offset → ∀ (x : E) (η : F) (v : Fin n → E × F),
        p B x ≤ Kp → q B η ≤ Kq → (∀ i, pairGrading p q B (v i) ≤ 1) →
        oneHighVariationWeight p oldBase (a + oldLoss) x (fun i => (v i).1) * q c η ≤
          C * (1 + pairGrading p q (s + L) (x, η) +
            ∑ i : Fin n, pairGrading p q (s + L) (v i)) := by
  obtain ⟨B, ℓ, hB, hinterp⟩ := hasInterpolation_mul_local_growth
    p q hp hq hIp hIq (offset + oldLoss) (max requestedBase oldBase)
    1 1 zero_le_one zero_le_one
  let L := max ℓ offset
  have hℓ : ℓ ≤ L := le_max_left _ _
  have hoff : offset ≤ L := le_max_right _ _
  have hb : oldBase ≤ B := (le_max_right _ _).trans hB
  refine ⟨B, L, hB, ?_⟩
  intro n Kp Kq hKp hKq s hs
  obtain ⟨C₀, hC₀, hunit⟩ := hinterp s hs
  let κp : ℝ := max Kp 1
  let κq : ℝ := max Kq 1
  let C₁ : ℝ := κp * κq * C₀
  have hκp : 1 ≤ κp := le_max_right _ _
  have hκq : 1 ≤ κq := le_max_right _ _
  have hC₁ : 0 ≤ C₁ :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hκp) (zero_le_one.trans hκq)) hC₀
  refine ⟨1 + ((n : ℝ) + 1) * C₁, by positivity, ?_⟩
  intro a c hac x η v hx hη hv
  let Q : ℝ := 1 + pairGrading p q (s + L) (x, η) +
    ∑ i : Fin n, pairGrading p q (s + L) (v i)
  have hx0 : 0 ≤ p (s + L) x := apply_nonneg _ _
  have hη0 : 0 ≤ q (s + L) η := apply_nonneg _ _
  have hsum0 : 0 ≤ ∑ i : Fin n, pairGrading p q (s + L) (v i) :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hvp (i : Fin n) : p B (v i).1 ≤ 1 := by
    have hh := hv i
    change p B (v i).1 + q B (v i).2 ≤ 1 at hh
    exact (le_add_of_nonneg_right (apply_nonneg _ _)).trans hh
  have hvlow (i : Fin n) : p oldBase (v i).1 ≤ 1 := (hp hb (v i).1).trans (hvp i)
  have hηhigh : q c η ≤ Q := by
    have hh := hq (show c ≤ s + L by omega) η
    dsimp only [Q]
    rw [pairGrading_apply]
    linarith only [hh, hx0, hsum0]
  have hprod (y : E) (hy : p B y ≤ κp) :
      p (a + oldLoss) y * q c η ≤ C₁ * (1 + p (s + ℓ) y + q (s + ℓ) η) :=
    seminorm_product_bound_on_larger_balls p q B (a + oldLoss) c (s + ℓ)
      hC₀ hκp hκq (hunit _ _ (by omega)) y η hy (hη.trans (le_max_left _ _))
  have hbaseProduct : p (a + oldLoss) x * q c η ≤ C₁ * Q := by
    apply (hprod x (hx.trans (le_max_left _ _))).trans
    apply mul_le_mul_of_nonneg_left _ hC₁
    have hhx := hp (Nat.add_le_add_left hℓ s) x
    have hhη := hq (Nat.add_le_add_left hℓ s) η
    dsimp only [Q]
    rw [pairGrading_apply]
    linarith only [hhx, hhη, hsum0]
  have hdirectionProduct (i : Fin n) :
      p (a + oldLoss) (v i).1 * q c η ≤ C₁ * Q := by
    apply (hprod (v i).1 ((hvp i).trans hκp)).trans
    apply mul_le_mul_of_nonneg_left _ hC₁
    have hhvi := hp (Nat.add_le_add_left hℓ s) (v i).1
    have hhη := hq (Nat.add_le_add_left hℓ s) η
    have hisum : p (s + L) (v i).1 ≤
        ∑ j : Fin n, pairGrading p q (s + L) (v j) :=
      (le_add_of_nonneg_right (apply_nonneg (q (s + L)) (v i).2)).trans
        (Finset.single_le_sum (f := fun j : Fin n => pairGrading p q (s + L) (v j))
          (fun j _ => apply_nonneg (pairGrading p q (s + L)) (v j)) (Finset.mem_univ i))
    dsimp only [Q]
    rw [pairGrading_apply]
    linarith only [hhvi, hhη, hisum, hx0]
  have hsum : (∑ i : Fin n, p (a + oldLoss) (v i).1 * q c η) ≤
      (n : ℝ) * (C₁ * Q) := by
    calc
      _ ≤ ∑ _i : Fin n, C₁ * Q := Finset.sum_le_sum (fun i _ => hdirectionProduct i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hone : oneHighVariationWeight p oldBase (a + oldLoss) x (fun i => (v i).1) ≤
      1 + p (a + oldLoss) x + ∑ i : Fin n, p (a + oldLoss) (v i).1 :=
    multilinearTameSize_le_affine (p oldBase) (p (a + oldLoss)) n
      (add_nonneg zero_le_one (apply_nonneg _ _)) (fun i => (v i).1) hvlow
  calc
    _ ≤ (1 + p (a + oldLoss) x + ∑ i : Fin n, p (a + oldLoss) (v i).1) * q c η :=
      mul_le_mul_of_nonneg_right hone (apply_nonneg _ _)
    _ = q c η + p (a + oldLoss) x * q c η +
        ∑ i : Fin n, p (a + oldLoss) (v i).1 * q c η := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ Q + C₁ * Q + (n : ℝ) * (C₁ * Q) :=
      add_le_add (add_le_add hηhigh hbaseProduct) hsum
    _ = _ := by dsimp only [Q]; ring

end ContinuousFlexibility.Statements
