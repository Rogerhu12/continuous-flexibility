module

public import ContinuousFlexibility.Statements.Analysis

/-!
# Homogeneous bounds for the Newton correction and error

The linear correction is the first jet in the residual variable at zero.
The bilinear error is the ordered second jet in the two independent residual
variables at zero. Evaluating the smooth tame estimates on these directions
gives homogeneous bounds for all residuals, including the kernels of the
base seminorm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section FiberJets

variable {Z X Y : Type*}
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [T2Space X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [T2Space Y]

omit [T2Space X] in
private theorem hasProjectiveCurveDerivAt_smul_zero (v : X) :
    HasProjectiveCurveDerivAt (fun t : ℝ => t • v) v 0 := by
  simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply, zero_add] using
    hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ X) 0 v

omit [T2Space Y] in
private theorem linear_fiber_firstJet {U : Set Z} {V : Z → Y →ₗ[ℝ] X}
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun p : Z × Y => V p.1 p.2))
    {z : Z} (hz : z ∈ U) (y : Y) :
    J.D 1 (z, 0) (Fin.cons (0, y) Fin.elim0) = V z y := by
  have h := J.derivative 0 (z, 0) ⟨hz, mem_univ _⟩ Fin.elim0 (0, y)
  have hcurve : (fun t : ℝ => J.D 0 ((z, 0) + t • ((0, y) : Z × Y)) Fin.elim0) =
      (fun t : ℝ => t • V z y) := by
    funext t
    have he : (z, 0) + t • ((0, y) : Z × Y) = (z, t • y) := by
      change (z + t • (0 : Z), (0 : Y) + t • y) = _
      simp only [smul_zero, add_zero, zero_add]
    rw [he]
    simpa only [map_smul] using J.zero (z, t • y) ⟨hz, mem_univ _⟩
  unfold HasProjectiveLineDerivAt at h
  rw [hcurve] at h
  exact h.unique (hasProjectiveCurveDerivAt_smul_zero (V z y))

private theorem bilinear_fiber_secondJet {U : Set Z} {Q : Z → Y →ₗ[ℝ] Y →ₗ[ℝ] Y}
    (J : Statements.SmoothDirections ((U ×ˢ univ) ×ˢ univ)
      (fun p : (Z × Y) × Y => Q p.1.1 p.1.2 p.2))
    {z : Z} (hz : z ∈ U) (r y : Y) :
    J.D 2 ((z, 0), 0) (Fin.cons ((0, r), 0) (Fin.cons (0, y) Fin.elim0)) = Q z r y := by
  let v : (Z × Y) × Y := ((0, r), 0)
  let w : (Z × Y) × Y := (0, y)
  have h := J.derivative 1 ((z, 0), 0) ⟨⟨hz, mem_univ _⟩, mem_univ _⟩
    (Fin.cons w Fin.elim0) v
  have hcurve : (fun t : ℝ => J.D 1 (((z, 0), 0) + t • v) (Fin.cons w Fin.elim0)) =
      (fun t : ℝ => t • Q z r y) := by
    funext t
    have he : ((z, 0), 0) + t • v = ((z, t • r), 0) := by
      change ((z + t • (0 : Z), (0 : Y) + t • r), (0 : Y) + t • (0 : Y)) = _
      simp only [smul_zero, add_zero, zero_add]
    rw [he]
    simpa only [w, LinearMap.map_smul₂] using
      linear_fiber_firstJet (V := fun p : Z × Y => Q p.1 p.2) J
        (z := (z, t • r)) ⟨hz, mem_univ _⟩ y
  unfold HasProjectiveLineDerivAt at h
  rw [hcurve] at h
  exact h.unique (hasProjectiveCurveDerivAt_smul_zero (Q z r y))

end FiberJets

section Estimates

variable {Z X Y : Type*}
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [T2Space X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [T2Space Y]

private theorem pairGrading_value
    {A B : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    (a : ℕ → Seminorm ℝ A) (b : ℕ → Seminorm ℝ B) (n : ℕ) (x : A) (y : B) :
    Statements.pairGrading a b n (x, y) = a n x + b n y := rfl

omit [T2Space Y] in
/-- A jointly smooth tame family of linear corrections has a homogeneous
linear tame estimate on a single base neighborhood. -/
theorem linearFamilyTame_on_ball_of_smoothTame
    {a : ℕ → Seminorm ℝ Z} {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set Z} {V : Z → Y →ₗ[ℝ] X}
    (hT : Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : Z × Y => V z.1 z.2))
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a base (z - z₀) < ε → ∀ y : Y,
          p s (V z y) ≤ C * (q (s + loss) y + (1 + a (s + loss) z) * q base y) := by
  obtain ⟨J, hJ⟩ := hT
  obtain ⟨loss, base, ε, hε, hbound⟩ := hJ 1 (z₀, 0) ⟨hz₀, mem_univ _⟩
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hbound s hs
  refine ⟨C, hC, ?_⟩
  intro z hz hlow y
  have hlow' : Statements.pairGrading a q base ((z, 0) - (z₀, 0)) < ε := by
    change Statements.pairGrading a q base (z - z₀, (0 : Y) - 0) < ε
    simpa only [pairGrading_value, sub_zero, map_zero, add_zero] using hlow
  let v : Fin 1 → Z × Y := Fin.cons (0, y) Fin.elim0
  have hv : v 0 = (0, y) := rfl
  have hjet : J.D 1 (z, 0) v = V z y := linear_fiber_firstJet J hz y
  have h := hbound (z, 0) ⟨hz, mem_univ _⟩ hlow' v
  have he : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simpa only [hjet, Fin.prod_univ_one, Fin.sum_univ_one, he, Finset.prod_empty,
    hv, pairGrading_value, map_zero, zero_add, add_zero, mul_one,
    add_comm ((1 + a (s + loss) z) * q base y) (q (s + loss) y)] using h

/-- A jointly smooth tame family of bilinear errors has a homogeneous tame
estimate in both independent residuals on a single base neighborhood. -/
theorem exists_bilinear_tame_bounds_on_ball_of_smoothTame
    {a : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ Y}
    {U : Set Z} {Q : Z → Y →ₗ[ℝ] Y →ₗ[ℝ] Y}
    (hT : Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ) (fun z : (Z × Y) × Y => Q z.1.1 z.1.2 z.2))
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a base (z - z₀) < ε → ∀ r y : Y,
          q s (Q z r y) ≤ C * ((1 + a (s + loss) z) * (q base r * q base y) +
            (q (s + loss) r * q base y + q base r * q (s + loss) y)) := by
  obtain ⟨J, hJ⟩ := hT
  obtain ⟨loss, base, ε, hε, hbound⟩ := hJ 2 ((z₀, 0), 0) ⟨⟨hz₀, mem_univ _⟩, mem_univ _⟩
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hbound s hs
  refine ⟨C, hC, ?_⟩
  intro z hz hlow r y
  have hlow' : Statements.pairGrading (Statements.pairGrading a q) q base
      (((z, 0), 0) - ((z₀, 0), 0)) < ε := by
    change Statements.pairGrading (Statements.pairGrading a q) q base
      ((z - z₀, (0 : Y) - 0), (0 : Y) - 0) < ε
    simpa only [pairGrading_value, sub_zero, map_zero, add_zero] using hlow
  let v : Fin 2 → (Z × Y) × Y := Fin.cons ((0, r), 0) (Fin.cons (0, y) Fin.elim0)
  have hv₀ : v 0 = ((0, r), 0) := rfl
  have hv₁ : v 1 = (0, y) := rfl
  have hjet : J.D 2 ((z, 0), 0) v = Q z r y := bilinear_fiber_secondJet J hz r y
  have h := hbound ((z, 0), 0) ⟨⟨hz, mem_univ _⟩, mem_univ _⟩ hlow' v
  have he₀ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he₁ : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simpa only [hjet, Fin.prod_univ_two, Fin.sum_univ_two, he₀, he₁, Finset.prod_singleton,
    hv₀, hv₁, pairGrading_value, map_zero, zero_add, add_zero,
    mul_comm (q (s + loss) y) (q base r)] using h

/-- Both correction estimates can use one base neighborhood and one loss.
Only the numerical constant may depend on the output order. -/
theorem exists_common_newton_correction_tame_bounds
    {a : ℕ → Seminorm ℝ Z} {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set Z} {V : Z → Y →ₗ[ℝ] X} {Q : Z → Y →ₗ[ℝ] Y →ₗ[ℝ] Y}
    (ha : Monotone a) (hq : Monotone q)
    (hV : Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : Z × Y => V z.1 z.2))
    (hQ : Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ) (fun z : (Z × Y) × Y => Q z.1.1 z.1.2 z.2))
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a base (z - z₀) < ε →
          (∀ y : Y, p s (V z y) ≤ C * (q (s + loss) y + (1 + a (s + loss) z) * q base y)) ∧
          (∀ r y : Y, q s (Q z r y) ≤ C * ((1 + a (s + loss) z) * (q base r * q base y) +
            (q (s + loss) r * q base y + q base r * q (s + loss) y))) := by
  obtain ⟨lV, bV, εV, hεV, HV⟩ := linearFamilyTame_on_ball_of_smoothTame hV hz₀
  obtain ⟨lQ, bQ, εQ, hεQ, HQ⟩ := exists_bilinear_tame_bounds_on_ball_of_smoothTame hQ hz₀
  let loss := max lV lQ
  let base := max bV bQ
  have hbV : bV ≤ base := le_max_left _ _
  have hbQ : bQ ≤ base := le_max_right _ _
  have hlV : lV ≤ loss := le_max_left _ _
  have hlQ : lQ ≤ loss := le_max_right _ _
  refine ⟨loss, base, min εV εQ, lt_min hεV hεQ, ?_⟩
  intro s hs
  obtain ⟨CV, hCV, hVest⟩ := HV s (hbV.trans hs)
  obtain ⟨CQ, hCQ, hQest⟩ := HQ s (hbQ.trans hs)
  let C := max CV CQ
  have hleV : CV ≤ C := le_max_left _ _
  have hleQ : CQ ≤ C := le_max_right _ _
  refine ⟨C, hCV.trans hleV, ?_⟩
  intro z hz hlow
  have hzV : a bV (z - z₀) < εV :=
    ((ha hbV (z - z₀)).trans_lt hlow).trans_le (min_le_left _ _)
  have hzQ : a bQ (z - z₀) < εQ :=
    ((ha hbQ (z - z₀)).trans_lt hlow).trans_le (min_le_right _ _)
  have hstate (l : ℕ) (hl : l ≤ loss) : 1 + a (s + l) z ≤ 1 + a (s + loss) z :=
    add_le_add le_rfl (ha (Nat.add_le_add_left hl s) z)
  have hstate₀ (l : ℕ) : 0 ≤ 1 + a (s + l) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hhigh (l : ℕ) (hl : l ≤ loss) (y : Y) : q (s + l) y ≤ q (s + loss) y :=
    hq (Nat.add_le_add_left hl s) y
  constructor
  · intro y
    have hm := add_le_add (hhigh lV hlV y)
      (mul_le_mul (hstate lV hlV) (hq hbV y) (apply_nonneg (q bV) y) (hstate₀ loss))
    have hnonneg := add_nonneg (apply_nonneg (q (s + loss)) y)
      (mul_nonneg (hstate₀ loss) (apply_nonneg (q base) y))
    exact (hVest z hz hzV y).trans
      ((mul_le_mul_of_nonneg_left hm hCV).trans (mul_le_mul_of_nonneg_right hleV hnonneg))
  · intro r y
    have hrr := mul_le_mul (hq hbQ r) (hq hbQ y)
      (apply_nonneg (q bQ) y) (apply_nonneg (q base) r)
    have hfirst := mul_le_mul (hstate lQ hlQ) hrr
      (mul_nonneg (apply_nonneg (q bQ) r) (apply_nonneg (q bQ) y)) (hstate₀ loss)
    have hsecond := mul_le_mul (hhigh lQ hlQ r) (hq hbQ y)
      (apply_nonneg (q bQ) y) (apply_nonneg (q (s + loss)) r)
    have hthird := mul_le_mul (hq hbQ r) (hhigh lQ hlQ y)
      (apply_nonneg (q (s + lQ)) y) (apply_nonneg (q base) r)
    have hnonneg := add_nonneg
      (mul_nonneg (hstate₀ loss) (mul_nonneg (apply_nonneg (q base) r) (apply_nonneg (q base) y)))
      (add_nonneg (mul_nonneg (apply_nonneg (q (s + loss)) r) (apply_nonneg (q base) y))
        (mul_nonneg (apply_nonneg (q base) r) (apply_nonneg (q (s + loss)) y)))
    exact (hQest z hz hzQ r y).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hfirst (add_le_add hsecond hthird)) hCQ).trans
        (mul_le_mul_of_nonneg_right hleQ hnonneg))

end Estimates

end ContinuousFlexibility.Analysis
