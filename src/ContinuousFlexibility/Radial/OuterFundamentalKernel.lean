import ContinuousFlexibility.Radial.OuterFundamentalPair

/-!
# Kernel identities and Robin uniqueness for the constructed pair

The determinant of the actual pair fixes the coefficient of the deep
Dirichlet solution.  Hence the deep kernel decomposition is proved from
the construction, and is not a hypothesis about the desired inverse.
A natural homogeneous state satisfying the normalized Robin condition
vanishes identically, even when the natural entrance value is zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

variable {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}

/-- The deep Dirichlet coefficient is fixed by the normalized determinant. -/
theorem OuterFundamentalStatePair.tail_coefficient
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0) :
    F.V c * F.tailB * ZQ c = 1 := by
  have hc : c ∈ Ico c b := ⟨le_rfl, hcb⟩
  have hUc : F.U c = F.tailA := by
    simpa only [hPc, hQc, mul_one, mul_zero, add_zero] using F.U_tail c hc
  have hZUc : F.ZU c = F.tailA * ZP c + F.tailB * ZQ c := F.ZU_tail c hc
  have hZVc : F.ZV c = F.V c * ZP c := by
    rw [F.ZV_tail c hc, F.V_tail c hc, hPc]
    ring
  have hdet := F.determinant c ⟨hac, hcb⟩
  rw [hUc, hZUc, hZVc] at hdet
  linear_combination -hdet

theorem OuterFundamentalStatePair.tail_dirichlet_identity
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0) :
    ∀ x ∈ Ico c b, F.V c * F.U x - F.U c * F.V x = Q x / ZQ c := by
  have hcoef := F.tail_coefficient hac hcb hPc hQc
  have hZQc : ZQ c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcoef
    norm_num at hcoef
  have hratio : F.V c * F.tailB = 1 / ZQ c := (eq_div_iff hZQc).mpr hcoef
  have hUc : F.U c = F.tailA := by
    simpa only [hPc, hQc, mul_one, mul_zero, add_zero] using
      F.U_tail c ⟨le_rfl, hcb⟩
  intro x hx
  rw [F.U_tail x hx, F.V_tail_factor hcb hPc x hx, hUc]
  calc
    _ = (F.V c * F.tailB) * Q x := by ring
    _ = Q x / ZQ c := by rw [hratio]; ring

/-- The actual full Green kernel on the deep tail is the Dirichlet
kernel plus the rank-one diagonal correction. -/
theorem OuterFundamentalStatePair.green_tail_decomposition
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam x y : ℝ} (hlam : lam ≠ 0)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hx : x ∈ Ico c b) (hy : y ∈ Ico c b) :
    outerGreenKernel lam F.U F.V x y =
      Q (min x y) * P (max x y) / (lam * ZQ c) +
        outerGreenKernel lam F.U F.V c c * (P x * P y) := by
  have hcoef := F.tail_coefficient hac hcb hPc hQc
  have hZQc : ZQ c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcoef
    norm_num at hcoef
  have hmin : min x y ∈ Ico c b :=
    ⟨le_min hx.1 hy.1, (min_le_left _ _).trans_lt hx.2⟩
  have hmax : max x y ∈ Ico c b :=
    ⟨hx.1.trans (le_max_left _ _), max_lt hx.2 hy.2⟩
  have hleft : F.V c * F.U (min x y) =
      Q (min x y) / ZQ c + F.U c * F.V c * P (min x y) := by
    have h := F.tail_dirichlet_identity hac hcb hPc hQc (min x y) hmin
    rw [F.V_tail_factor hcb hPc (min x y) hmin] at h
    linear_combination h
  have hprod : P (min x y) * P (max x y) = P x * P y := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, max_eq_right hxy]
    · rw [min_eq_right hyx, max_eq_left hyx, mul_comm]
  calc
    outerGreenKernel lam F.U F.V x y =
        lam⁻¹ * ((F.V c * F.U (min x y)) * P (max x y)) := by
      rw [outerGreenKernel, F.V_tail_factor hcb hPc (max x y) hmax]
      ring
    _ = Q (min x y) * P (max x y) / (lam * ZQ c) +
        (lam⁻¹ * (F.U c * F.V c)) * (P (min x y) * P (max x y)) := by
      rw [hleft]
      field_simp [hlam, hZQc] <;> ring
    _ = _ := by rw [hprod, outerGreenKernel_self]

/-- The usual physical Dirichlet normalization has unit outward flux. -/
theorem OuterFundamentalStatePair.green_tail_decomposition_unit_flux
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam x y : ℝ} (hlam : lam ≠ 0)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam) (hx : x ∈ Ico c b) (hy : y ∈ Ico c b) :
    outerGreenKernel lam F.U F.V x y =
      Q (min x y) * P (max x y) +
        outerGreenKernel lam F.U F.V c c * (P x * P y) := by
  have hden : lam * ZQ c = 1 := by rw [hflux]; field_simp [hlam]
  simpa only [hden, div_one] using
    F.green_tail_decomposition hlam hac hcb hPc hQc hx hy

/-- A natural homogeneous state satisfying the actual Robin condition is zero.
The natural-line classification is needed only on the deep tail. -/
theorem OuterFundamentalStatePair.robin_unique_state
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b)
    (hα : ∀ x ∈ Ioo c b, alpha x ≠ 0)
    {u z : ℝ → ℝ} (hstate : OuterFirstOrderSystem alpha beta u z (Ico a b))
    (hRobin : outerStatePair F.entrance (u a, z a) = 0)
    (hnatural : ∃ C : ℝ, ∀ x ∈ Ioo c b, u x = C * P x) :
    ∀ x ∈ Ico a b, u x = 0 ∧ z x = 0 := by
  obtain ⟨C, hC⟩ := hnatural
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have hd : d ∈ Ico a b := ⟨hac.trans hcd.le, hdb⟩
  have ha : a ∈ Ico a b := ⟨le_rfl, hac.trans_lt hcb⟩
  have hvalue : u =ᶠ[𝓝 d] fun x => (C * F.scale) * F.V x := by
    filter_upwards [Ioo_mem_nhds hcd hdb] with x hx
    rw [hC x hx, F.V_tail x ⟨hx.1.le, hx.2⟩]
    field_simp [F.scale_pos.ne'] <;> ring
  have hder := ((F.V_system d hd).1.const_mul (C * F.scale)).congr_of_eventuallyEq hvalue
  have hz : z d = (C * F.scale) * F.ZV d := by
    apply (mul_left_cancel₀ (hα d ⟨hcd, hdb⟩))
    calc
      alpha d * z d = (C * F.scale) * (alpha d * F.ZV d) :=
        (hstate d hd).1.unique hder
      _ = alpha d * ((C * F.scale) * F.ZV d) := by ring
  have hdetd : u d * F.ZV d - z d * F.V d = 0 := by
    rw [hvalue.eq_of_nhds, hz]
    ring
  have hdeta : u a * F.ZV a - z a * F.V a = 0 :=
    (outerFirstOrderSystem_state_determinant (convex_Ico a b)
      hstate F.V_system ha hd).symm.trans hdetd
  have hva : F.V a = F.entrance.1 := congrArg Prod.fst F.V_initial
  have hza : F.ZV a = F.entrance.2 := congrArg Prod.snd F.V_initial
  rw [hva, hza] at hdeta
  change F.entrance.1 * u a + F.entrance.2 * z a = 0 at hRobin
  have hu0 : u a = 0 := by
    linear_combination F.entrance.1 * hRobin + F.entrance.2 * hdeta - u a * F.unit
  have hz0 : z a = 0 := by
    linear_combination F.entrance.2 * hRobin - F.entrance.1 * hdeta - z a * F.unit
  intro x hx
  have hVdet : u x * F.ZV x - z x * F.V x = 0 := by
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b)
      hstate F.V_system ha hx, hu0, hz0, zero_mul, zero_mul, sub_self]
  have hUdet : F.U x * z x - F.ZU x * u x = 0 := by
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b)
      F.U_system hstate ha hx, hu0, hz0, mul_zero, mul_zero, sub_self]
  have hFdet := F.determinant x hx
  constructor
  · linear_combination -F.U x * hVdet - F.V x * hUdet + u x * hFdet
  · linear_combination -F.ZU x * hVdet - F.ZV x * hUdet + z x * hFdet

end ContinuousFlexibility.Radial
