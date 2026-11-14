module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonRecurrence
public import ContinuousFlexibility.Analysis.ProjectiveNewtonCorrectionBounds

/-!
# Common tame estimates for the Newton iteration

The residual and its first two directional jets, the linear correction, and
the bilinear error use the same finite base, loss, and radius. The base can
be chosen above the original domain base and both smoothing bases.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency false

theorem pairGrading_monotone
    {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (hp : Monotone p) (hq : Monotone q) :
    Monotone (Statements.pairGrading p q) := by
  intro m n hmn z
  change p m z.1 + q m z.2 ≤ p n z.1 + q n z.2
  exact add_le_add (hp hmn z.1) (hq hmn z.2)

private theorem tame_bound_enlarge {v L H c C : ℝ}
    (hv : v ≤ c * L) (hc : 0 ≤ c) (hcC : c ≤ C) (hLH : L ≤ H) (hH : 0 ≤ H) :
    v ≤ C * H :=
  hv.trans ((mul_le_mul_of_nonneg_left hLH hc).trans (mul_le_mul_of_nonneg_right hcC hH))

/-- Extract the estimates used in the fixed-parameter Newton recurrence
from the three original smooth tame maps. -/
theorem exists_common_newton_tame_data
    {Z X Y : Type*}
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [T2Space X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [T2Space Y]
    {a : ℕ → Seminorm ℝ Z} {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set Z} {R : Z → Y} {V : Z → Y →ₗ[ℝ] X} {Q : Z → Y →ₗ[ℝ] Y →ₗ[ℝ] Y}
    (ha : Monotone a) (hq : Monotone q) (bMin : ℕ)
    (hR : Statements.SmoothTameOn a q U R)
    (hV : Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : Z × Y => V z.1 z.2))
    (hQ : Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ) (fun z : (Z × Y) × Y => Q z.1.1 z.1.2 z.2))
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ J : Statements.SmoothDirections U R, ∃ b l : ℕ, ∃ ε : ℝ,
      bMin ≤ b ∧ 0 < ε ∧ ∀ s : ℕ, b ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a b (z - z₀) < ε →
          (q s (R z) ≤ C * (1 + a (s + l) z)) ∧
          (∀ d : Z,
            (q s (projectiveJetHeadLinear J.D 0 z Fin.elim0 d) ≤
              C * ((1 + a (s + l) z) * a b d + a (s + l) d)) ∧
            (q s (J.D 2 z (Fin.cons d (Fin.cons d Fin.elim0))) ≤
              C * ((1 + a (s + l) z) * (a b d) ^ 2 + 2 * (a (s + l) d * a b d)))) ∧
          (∀ y : Y, p s (V z y) ≤ C * (q (s + l) y + (1 + a (s + l) z) * q b y)) ∧
          (∀ r y : Y, q s (Q z r y) ≤ C * ((1 + a (s + l) z) * (q b r * q b y) +
            (q (s + l) r * q b y + q b r * q (s + l) y))) := by
  obtain ⟨l₀, b₀, ε₀, hε₀, H₀⟩ := exists_zero_tame_bound hR hz₀
  obtain ⟨J, bJ, lJ, εJ, hεJ, HJ⟩ := exists_common_newton_tame_bounds hR ha hz₀
  obtain ⟨lV, bV, εV, hεV, HV⟩ := exists_common_newton_correction_tame_bounds ha hq hV hQ hz₀
  let b := max bMin (max b₀ (max bJ bV))
  let l := max l₀ (max lJ lV)
  let ε := min ε₀ (min εJ εV)
  have hb₀ : b₀ ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hbJ : bJ ≤ b := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbV : bV ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hl₀ : l₀ ≤ l := le_max_left _ _
  have hlJ : lJ ≤ l := (le_max_left _ _).trans (le_max_right _ _)
  have hlV : lV ≤ l := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨J, b, l, ε, le_max_left _ _, lt_min hε₀ (lt_min hεJ hεV), ?_⟩
  intro s hs
  obtain ⟨C₀, hC₀, hR₀⟩ := H₀ s (hb₀.trans hs)
  obtain ⟨CJ, hCJ, hJ⟩ := HJ s (hbJ.trans hs)
  obtain ⟨CV, hCV, hVQ⟩ := HV s (hbV.trans hs)
  let C := C₀ + CJ + CV
  have hC₀' : C₀ ≤ C := by dsimp only [C]; linarith only [hCJ, hCV]
  have hCJ' : CJ ≤ C := by dsimp only [C]; linarith only [hC₀, hCV]
  have hCV' : CV ≤ C := by dsimp only [C]; linarith only [hC₀, hCJ]
  refine ⟨C, hC₀.trans hC₀', ?_⟩
  intro z hz hnear
  have hnear₀ : a b₀ (z - z₀) < ε₀ :=
    ((ha hb₀ (z - z₀)).trans_lt hnear).trans_le (min_le_left _ _)
  have hnearJ : a bJ (z - z₀) < εJ :=
    ((ha hbJ (z - z₀)).trans_lt hnear).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hnearV : a bV (z - z₀) < εV :=
    ((ha hbV (z - z₀)).trans_lt hnear).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hstate (l' : ℕ) (hl' : l' ≤ l) : 1 + a (s + l') z ≤ 1 + a (s + l) z :=
    add_le_add le_rfl (ha (Nat.add_le_add_left hl' s) z)
  have hstate₀ : 0 ≤ 1 + a (s + l) z := add_nonneg zero_le_one (apply_nonneg _ _)
  obtain ⟨hVbound, hQbound⟩ := hVQ z hz hnearV
  refine ⟨tame_bound_enlarge (hR₀ z hz hnear₀) hC₀ hC₀' (hstate l₀ hl₀) hstate₀, ?_, ?_, ?_⟩
  · intro d
    obtain ⟨hJ₁, hJ₂⟩ := hJ z hz hnearJ d
    have hlow : a bJ d ≤ a b d := ha hbJ d
    have hhigh : a (s + lJ) d ≤ a (s + l) d := ha (Nat.add_le_add_left hlJ s) d
    have hlow₀ : 0 ≤ a b d := apply_nonneg _ _
    have hhigh₀ : 0 ≤ a (s + l) d := apply_nonneg _ _
    have hfirst := add_le_add
      (mul_le_mul (hstate lJ hlJ) hlow (apply_nonneg _ _) hstate₀) hhigh
    have hsecond := add_le_add
      (mul_le_mul (hstate lJ hlJ) (pow_le_pow_left₀ (apply_nonneg _ _) hlow 2)
        (sq_nonneg _) hstate₀)
      (mul_le_mul_of_nonneg_left (mul_le_mul hhigh hlow (apply_nonneg _ _) hhigh₀)
        (show (0 : ℝ) ≤ 2 by norm_num))
    exact ⟨tame_bound_enlarge hJ₁ hCJ hCJ' hfirst
        (add_nonneg (mul_nonneg hstate₀ hlow₀) hhigh₀),
      tame_bound_enlarge hJ₂ hCJ hCJ' hsecond
        (add_nonneg (mul_nonneg hstate₀ (sq_nonneg _))
          (mul_nonneg (by norm_num) (mul_nonneg hhigh₀ hlow₀)))⟩
  · intro y
    have hlow : q bV y ≤ q b y := hq hbV y
    have hhigh : q (s + lV) y ≤ q (s + l) y := hq (Nat.add_le_add_left hlV s) y
    exact tame_bound_enlarge (hVbound y) hCV hCV'
      (add_le_add hhigh (mul_le_mul (hstate lV hlV) hlow (apply_nonneg _ _) hstate₀))
      (add_nonneg (apply_nonneg _ _) (mul_nonneg hstate₀ (apply_nonneg _ _)))
  · intro r y
    have hlo (u : Y) : q bV u ≤ q b u := hq hbV u
    have hhi (u : Y) : q (s + lV) u ≤ q (s + l) u := hq (Nat.add_le_add_left hlV s) u
    have hr₀ : 0 ≤ q b r := apply_nonneg _ _
    have hy₀ : 0 ≤ q b y := apply_nonneg _ _
    have hr₁ : 0 ≤ q (s + l) r := apply_nonneg _ _
    have hy₁ : 0 ≤ q (s + l) y := apply_nonneg _ _
    have hprod := mul_le_mul (hlo r) (hlo y) (apply_nonneg _ _) hr₀
    have hfirst := mul_le_mul (hstate lV hlV) hprod
      (mul_nonneg (apply_nonneg (q bV) r) (apply_nonneg (q bV) y)) hstate₀
    have hsecond := mul_le_mul (hhi r) (hlo y) (apply_nonneg _ _) hr₁
    have hthird := mul_le_mul (hlo r) (hhi y) (apply_nonneg _ _) hr₀
    exact tame_bound_enlarge (hQbound r y) hCV hCV'
      (add_le_add hfirst (add_le_add hsecond hthird))
      (add_nonneg (mul_nonneg hstate₀ (mul_nonneg hr₀ hy₀))
        (add_nonneg (mul_nonneg hr₁ hy₀) (mul_nonneg hr₀ hy₁)))

end ContinuousFlexibility.Analysis
