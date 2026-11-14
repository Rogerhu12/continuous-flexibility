module

public import ContinuousFlexibility.Analysis.StateNeighborhood
public import ContinuousFlexibility.Analysis.SpacesInterpolationProducts

/-!
# Interpolation on the actual nonlinear state grading

The height, scalar and two circle factors all use their existing
projective seminorms. Interpolation is stable under their finite sum,
so the one-high product estimate applies with one fixed state loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem coordinate_interpolation_exponent_mono
    {A B θ φ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hθφ : θ ≤ φ) (hφ : φ < 1) :
    A ^ (1 - θ) * B ^ θ ≤ A ^ (1 - φ) * B ^ φ := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hz : A = 0
  · rw [hz, Real.zero_rpow (by linarith : 1 - θ ≠ 0), zero_mul]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hB _)
  have ha : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hb : 0 < B := ha.trans_le hAB
  have he (t : ℝ) : A ^ (1 - t) * B ^ t = A * (B / A) ^ t := by
    rw [Real.rpow_sub ha, Real.rpow_one, Real.div_rpow hb.le ha.le]
    ring
  rw [he θ, he φ]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ((one_le_div ha).mpr hAB) hθφ) hA

/-- Pairing two increasing interpolation gradings retains a fixed loss. -/
theorem coordinate_hasInterpolation_pair
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q) :
    HasInterpolation (pairGrading p q) := by
  obtain ⟨bp, lp, hIp⟩ := hIp
  obtain ⟨bq, lq, hIq⟩ := hIq
  let ell := max lp lq
  refine ⟨max bp bq, ell, ?_⟩
  intro a b c ha hab hbc
  have hbp : bp ≤ a := (le_max_left _ _).trans ha
  have hbq : bq ≤ a := (le_max_right _ _).trans ha
  have hlp : lp ≤ ell := le_max_left _ _
  have hlq : lq ≤ ell := le_max_right _ _
  obtain ⟨Cp, hCp, hpb⟩ := hIp a b c hbp hab
    ((Nat.add_le_add_left hlp b).trans_lt hbc)
  obtain ⟨Cq, hCq, hqb⟩ := hIq a b c hbq hab
    ((Nat.add_le_add_left hlq b).trans_lt hbc)
  refine ⟨Cp + Cq, add_nonneg hCp hCq, ?_⟩
  intro z
  let L : ℝ := pairGrading p q a z
  let H : ℝ := pairGrading p q c z
  let d : ℝ := (c : ℝ) - a
  let θ (r : ℕ) : ℝ := ((b : ℝ) - a + r) / d
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbcR : (b : ℝ) + ell < c := by exact_mod_cast hbc
  have hellR : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hd : 0 < d := by dsimp only [d]; linarith only [habR, hbcR, hellR]
  have hL : 0 ≤ L := apply_nonneg _ _
  have hac : a ≤ c := by omega
  have hLH : L ≤ H := add_le_add (hp hac z.1) (hq hac z.2)
  have hθ0 (r : ℕ) : 0 ≤ θ r :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) r]) hd.le
  have hθell : θ ell < 1 := by
    apply (div_lt_one hd).mpr
    dsimp only [d]
    linarith only [hbcR]
  have hθle (r : ℕ) (hr : r ≤ ell) : θ r ≤ θ ell := by
    apply div_le_div_of_nonneg_right _ hd.le
    have hrr : (r : ℝ) ≤ ell := by exact_mod_cast hr
    linarith only [hrr]
  have hlow (r : ℕ) :
      ((c : ℝ) - b - r) / ((c : ℝ) - a) = 1 - θ r := by
    change ((c : ℝ) - b - r) / d = 1 - ((b : ℝ) - a + r) / d
    field_simp [hd.ne']
    dsimp only [d]
    ring
  have hdom (r : ℕ) (hr : r ≤ ell) (u v : ℝ)
      (hu : 0 ≤ u) (hv : 0 ≤ v) (huL : u ≤ L) (hvH : v ≤ H) :
      u ^ (((c : ℝ) - b - r) / ((c : ℝ) - a)) *
          v ^ (((b : ℝ) - a + r) / ((c : ℝ) - a)) ≤
        L ^ (((c : ℝ) - b - ell) / ((c : ℝ) - a)) *
          H ^ (((b : ℝ) - a + ell) / ((c : ℝ) - a)) := by
    rw [hlow r, hlow ell]
    change u ^ (1 - θ r) * v ^ θ r ≤ L ^ (1 - θ ell) * H ^ θ ell
    have hr1 : θ r < 1 := (hθle r hr).trans_lt hθell
    apply le_trans (mul_le_mul
      (Real.rpow_le_rpow hu huL (sub_nonneg.mpr hr1.le))
      (Real.rpow_le_rpow hv hvH (hθ0 r))
      (Real.rpow_nonneg hv _) (Real.rpow_nonneg hL _))
    exact coordinate_interpolation_exponent_mono hL hLH (hθle r hr) hθell
  let Z : ℝ := L ^ (((c : ℝ) - b - ell) / ((c : ℝ) - a)) *
    H ^ (((b : ℝ) - a + ell) / ((c : ℝ) - a))
  have hpa : p a z.1 ≤ L := le_add_of_nonneg_right (apply_nonneg _ _)
  have hqa : q a z.2 ≤ L := le_add_of_nonneg_left (apply_nonneg _ _)
  have hpc : p c z.1 ≤ H := le_add_of_nonneg_right (apply_nonneg _ _)
  have hqc : q c z.2 ≤ H := le_add_of_nonneg_left (apply_nonneg _ _)
  have hP : p b z.1 ≤ Cp * Z := by
    have hfirst := hpb z.1
    rw [mul_assoc] at hfirst
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left
        (hdom lp hlp _ _ (apply_nonneg _ _) (apply_nonneg _ _) hpa hpc) hCp)
  have hQ : q b z.2 ≤ Cq * Z := by
    have hfirst := hqb z.2
    rw [mul_assoc] at hfirst
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left
        (hdom lq hlq _ _ (apply_nonneg _ _) (apply_nonneg _ _) hqa hqc) hCq)
  change p b z.1 + q b z.2 ≤ (Cp + Cq) * L ^ _ * H ^ _
  calc
    _ ≤ Cp * Z + Cq * Z := add_le_add hP hQ
    _ = _ := by dsimp only [Z]; ring

theorem coordinate_hasInterpolation_realGrading : HasInterpolation realGrading := by
  refine ⟨0, 0, ?_⟩
  intro a b c _ hab hbc
  refine ⟨1, zero_le_one, ?_⟩
  intro x
  simp only [realGrading, coe_normSeminorm, Nat.cast_zero, sub_zero, add_zero, one_mul]
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    positivity
  have hx0 : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have hac : a < c := by omega
  have hd : (c : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hac)
  have he : ((c : ℝ) - b) / (c - a) + ((b : ℝ) - a) / (c - a) = 1 := by
    field_simp [hd]
    ring
  rw [← Real.rpow_add hx0, he, Real.rpow_one]

/-- The actual nonlinear state grading inherits interpolation from the
physical height and circle models fixed in the frozen statement. -/
theorem coordinate_hasInterpolation_stateGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) : HasInterpolation (stateGrading S) := by
  have hH : HasInterpolation (S.height (3 / 4 : ℝ)).grading :=
    (hS.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hC : HasInterpolation (S.circle (3 / 4 : ℝ)).grading :=
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hHm : Monotone (S.height (3 / 4 : ℝ)).grading := gradedSeminorm_monotone _ _
  have hCm : Monotone (S.circle (3 / 4 : ℝ)).grading := gradedSeminorm_monotone _ _
  have hRm : Monotone realGrading := fun _ _ _ => le_rfl
  exact coordinate_hasInterpolation_pair (heightPairGrading_monotone S)
    (tamePairGrading_monotone hRm (tamePairGrading_monotone hCm hCm))
    (coordinate_hasInterpolation_pair hHm hRm hH coordinate_hasInterpolation_realGrading)
    (coordinate_hasInterpolation_pair hRm (tamePairGrading_monotone hCm hCm)
      coordinate_hasInterpolation_realGrading (coordinate_hasInterpolation_pair hCm hCm hC hC))

/-- One base and one loss control every finite state-jet product. -/
theorem coordinate_state_jet_product_oneHigh
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (order : ι → ℕ) (s : ℕ), (∑ i, order i) ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → AnnularState S,
          (∏ i, stateGrading S (order i + 2) (x i)) ≤ C *
            ∑ i, stateGrading S (s + loss) (x i) *
              ∏ j ∈ Finset.univ.erase i, stateGrading S base (x j) :=
  spaces_interpolation_product_bound (stateGrading S)
    (fun x _ _ h => stateGrading_monotone S h x)
    (coordinate_hasInterpolation_stateGrading hS)

end ContinuousFlexibility.Analysis
