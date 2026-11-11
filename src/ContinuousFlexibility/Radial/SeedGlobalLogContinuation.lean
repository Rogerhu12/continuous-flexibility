import ContinuousFlexibility.Radial.SeedLogSystem
import ContinuousFlexibility.Radial.SeedConeModes
import ContinuousFlexibility.Radial.SeedPositiveLogExtension
import ContinuousFlexibility.Radial.MorseChainLocalGluing

/-!
# Global log-radius solutions with exact cone ends

A finite Cauchy solution is continued beyond both ends by its actual
homogeneous cone coefficients. All joins use equality on open collars.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

def seedConeLogHeight (A B y : ℝ) : ℝ := A * exp (2 * y) + B * exp (-2 * y)

def seedConeLogVelocity (A B y : ℝ) : ℝ := 2 * A * exp (2 * y) - 2 * B * exp (-2 * y)

theorem seedConeLogHeight_smooth (A B : ℝ) : ContDiff ℝ ∞ (seedConeLogHeight A B) :=
  (contDiff_const.mul (contDiff_const.mul contDiff_id).exp).add
    (contDiff_const.mul (contDiff_const.mul contDiff_id).exp)

theorem hasDerivAt_seedConeLogHeight (A B y : ℝ) :
    HasDerivAt (seedConeLogHeight A B) (seedConeLogVelocity A B y) y := by
  have h := (((hasDerivAt_id y).const_mul 2).exp.const_mul A).add
    (((hasDerivAt_id y).const_mul (-2)).exp.const_mul B)
  apply h.congr_deriv
  simp only [seedConeLogVelocity, id_eq]
  ring

theorem hasDerivAt_seedConeLogVelocity (A B y : ℝ) :
    HasDerivAt (seedConeLogVelocity A B) (4 * seedConeLogHeight A B y) y := by
  have h := (((hasDerivAt_id y).const_mul 2).exp.const_mul (2 * A)).sub
    (((hasDerivAt_id y).const_mul (-2)).exp.const_mul (2 * B))
  apply h.congr_deriv
  simp only [seedConeLogHeight, id_eq]
  ring

theorem seedConeLogHeight_secondDeriv (A B y : ℝ) :
    deriv (deriv (seedConeLogHeight A B)) y = 4 * seedConeLogHeight A B y := by
  have he : deriv (seedConeLogHeight A B) = seedConeLogVelocity A B :=
    funext (fun t => (hasDerivAt_seedConeLogHeight A B t).deriv)
  rw [he, (hasDerivAt_seedConeLogVelocity A B y).deriv]

theorem seedLogEquation_of_germ {u v : ℝ → ℝ} {p y : ℝ}
    (h : u =ᶠ[𝓝 y] v)
    (hv : deriv (deriv v) y = (1 - p) * deriv v y + 4 * p * v y) :
    deriv (deriv u) y = (1 - p) * deriv u y + 4 * p * u y := by
  have h₂ : deriv (deriv u) y = deriv (deriv v) y := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.iteratedDeriv_eq 2
  rw [h₂, h.deriv_eq, h.eq_of_nhds]
  exact hv

theorem seedLogSystem_secondDeriv {p v z : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hs : ∀ y ∈ J, HasDerivAt v (z y) y ∧
      HasDerivAt z ((1 - p y) * z y + 4 * p y * v y) y) :
    ∀ y ∈ J, deriv (deriv v) y = (1 - p y) * deriv v y + 4 * p y * v y := by
  intro y hy
  have hloc : deriv v =ᶠ[𝓝 y] z :=
    Filter.eventuallyEq_of_mem (hJ.mem_nhds hy) (fun t ht => (hs t ht).1.deriv)
  rw [hloc.deriv_eq, (hs y hy).2.deriv, (hs y hy).1.deriv]

structure SeedGlobalLogContinuation (H : ℝ → ℝ) (left right y₀ A B : ℝ) where
  height : ℝ → ℝ
  smooth : ContDiff ℝ ∞ height
  value : height y₀ = A
  deriv_value : deriv height y₀ = B
  equation : ∀ y, deriv (deriv height) y =
    (1 - deriv H y) * deriv height y + 4 * deriv H y * height y
  nonzero : ∀ y, (height y, deriv height y) ≠ (0, 0)
  leftA : ℝ
  leftB : ℝ
  rightA : ℝ
  rightB : ℝ
  left_ne : (leftA, leftB) ≠ (0, 0)
  right_ne : (rightA, rightB) ≠ (0, 0)
  left_modes : ∀ y, y ≤ left → height y = seedConeLogHeight leftA leftB y
  right_modes : ∀ y, right ≤ y → height y = seedConeLogHeight rightA rightB y

theorem exists_seedGlobalLogContinuation {f : ℝ → ℝ} {y₀ : ℝ}
    (E : SeedPositiveLogExtension f y₀) (A B : ℝ) (hAB : (A, B) ≠ (0, 0)) :
    Nonempty (SeedGlobalLogContinuation E.logProfile (E.left - 1) (E.right + 1) y₀ A B) := by
  have hy₀ : y₀ ∈ Icc (E.left - 2) (E.right + 2) :=
    ⟨by linarith only [E.left_lt], by linarith only [E.right_gt]⟩
  obtain ⟨v, z, hvs, hzs, hv₀, hz₀, hd⟩ := exists_seedLogSystem E.smooth hy₀ A B
  have heq := seedLogSystem_secondDeriv isOpen_Ioo hd
  let L := E.left - 1
  let R := E.right + 1
  have hL₀ : L < y₀ := by dsimp only [L]; linarith only [E.left_lt]
  have hR₀ : y₀ < R := by dsimp only [R]; linarith only [E.right_gt]
  have hLR : L < R := hL₀.trans hR₀
  have hsubL : Ioo (E.left - 2) E.left ⊆ Ioo (E.left - 2 - 1) (E.right + 2 + 1) := by
    intro y hy
    exact ⟨by linarith only [hy.1], by linarith only [hy.2, E.left_lt, E.right_gt]⟩
  have hsubR : Ioo E.right (E.right + 2) ⊆ Ioo (E.left - 2 - 1) (E.right + 2 + 1) := by
    intro y hy
    exact ⟨by linarith only [hy.1, E.left_lt, E.right_gt], by linarith only [hy.2]⟩
  have hLs : ∀ y ∈ Ioo (E.left - 2) E.left,
      deriv (deriv v) y = (2 : ℝ) ^ 2 * v y := by
    intro y hy
    rw [heq y (hsubL hy), E.left_cone y hy.2.le]
    norm_num
  have hRs : ∀ y ∈ Ioo E.right (E.right + 2),
      deriv (deriv v) y = (2 : ℝ) ^ 2 * v y := by
    intro y hy
    rw [heq y (hsubR hy), E.right_cone y hy.1.le]
    norm_num
  let AL := coneExponentialCoefficient v 2 L
  let BL := coneExponentialCoefficient v (-2) L
  let AR := coneExponentialCoefficient v 2 R
  let BR := coneExponentialCoefficient v (-2) R
  have hLe : EqOn v (seedConeLogHeight AL BL) (Ioo (E.left - 2) E.left) := by
    intro y hy
    exact eq_coneExponential_modes (s := (2 : ℝ)) (by norm_num) isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (show L ∈ Ioo (E.left - 2) E.left by dsimp only [L]; constructor <;> linarith)
      (fun t _ => hvs.differentiable (by simp) t)
      (fun t _ => (contDiff_infty_iff_deriv.mp hvs).2.differentiable (by simp) t)
      hLs y hy
  have hRe : EqOn v (seedConeLogHeight AR BR) (Ioo E.right (E.right + 2)) := by
    intro y hy
    exact eq_coneExponential_modes (s := (2 : ℝ)) (by norm_num) isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (show R ∈ Ioo E.right (E.right + 2) by dsimp only [R]; constructor <;> linarith)
      (fun t _ => hvs.differentiable (by simp) t)
      (fun t _ => (contDiff_infty_iff_deriv.mp hvs).2.differentiable (by simp) t)
      hRs y hy
  have hLm : seedConeLogHeight AL BL =ᶠ[𝓝 L] v :=
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhds
      (show E.left - 2 < L by dsimp only [L]; linarith)
      (show L < E.left by dsimp only [L]; linarith)) hLe).symm
  have hRm : v =ᶠ[𝓝 R] seedConeLogHeight AR BR :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds
      (show E.right < R by dsimp only [R]; linarith)
      (show R < E.right + 2 by dsimp only [R]; linarith)) hRe
  let G := morseGlueCut R v (seedConeLogHeight AR BR)
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_morseGlueCut hvs (seedConeLogHeight_smooth AR BR) hRm
  have hLG : seedConeLogHeight AL BL =ᶠ[𝓝 L] G :=
    hLm.trans (morseGlueCut_eventually_left hRm hLR.le).symm
  let F := morseGlueCut L (seedConeLogHeight AL BL) G
  have hFs : ContDiff ℝ ∞ F :=
    contDiff_morseGlueCut (seedConeLogHeight_smooth AL BL) hGs hLG
  have hleft (y : ℝ) (hy : y ≤ L) : F =ᶠ[𝓝 y] seedConeLogHeight AL BL :=
    morseGlueCut_eventually_left hLG hy
  have hmid (y : ℝ) (hyL : L ≤ y) (hyR : y ≤ R) : F =ᶠ[𝓝 y] v :=
    (morseGlueCut_eventually_right hLG hyL).trans (morseGlueCut_eventually_left hRm hyR)
  have hright (y : ℝ) (hy : R ≤ y) : F =ᶠ[𝓝 y] seedConeLogHeight AR BR :=
    (morseGlueCut_eventually_right hLG (hLR.le.trans hy)).trans
      (morseGlueCut_eventually_right hRm hy)
  have hF₀ : F y₀ = A := (hmid y₀ hL₀.le hR₀.le).eq_of_nhds.trans hv₀
  have hd₀ : deriv F y₀ = B := by
    rw [(hmid y₀ hL₀.le hR₀.le).deriv_eq]
    exact (hd y₀ ⟨by linarith only [E.left_lt], by linarith only [E.right_gt]⟩).1.deriv.trans hz₀
  have hFeq (y : ℝ) : deriv (deriv F) y =
      (1 - deriv E.logProfile y) * deriv F y + 4 * deriv E.logProfile y * F y := by
    by_cases hyL : y ≤ L
    · apply seedLogEquation_of_germ (hleft y hyL)
      rw [seedConeLogHeight_secondDeriv, E.left_cone y (by dsimp only [L] at hyL; linarith)]
      ring
    by_cases hyR : R ≤ y
    · apply seedLogEquation_of_germ (hright y hyR)
      rw [seedConeLogHeight_secondDeriv, E.right_cone y (by dsimp only [R] at hyR; linarith)]
      ring
    · apply seedLogEquation_of_germ (hmid y (le_of_lt (lt_of_not_ge hyL)) (le_of_lt (lt_of_not_ge hyR)))
      apply heq y
      dsimp only [L] at hyL
      dsimp only [R] at hyR
      exact ⟨by linarith, by linarith⟩
  have hFsys (y : ℝ) : HasDerivAt F (deriv F y) y ∧
      HasDerivAt (deriv F) ((1 - deriv E.logProfile y) * deriv F y +
        4 * deriv E.logProfile y * F y) y :=
    ⟨(hFs.differentiable (by simp) y).hasDerivAt,
      ((contDiff_infty_iff_deriv.mp hFs).2.differentiable (by simp) y).hasDerivAt.congr_deriv (hFeq y)⟩
  have hFn (y : ℝ) : (F y, deriv F y) ≠ (0, 0) := by
    have hn₀ : (F y₀, deriv F y₀) ≠ (0, 0) := by simpa only [hF₀, hd₀] using hAB
    exact seedLogSystem_state_ne_zero
      (contDiff_infty_iff_deriv.mp E.smooth).2.continuous.continuousOn
      (show y₀ ∈ Icc (min y₀ y) (max y₀ y) from ⟨min_le_left _ _, le_max_left _ _⟩)
      (fun t _ => hFsys t) hn₀ y ⟨min_le_right _ _, le_max_right _ _⟩
  have hAL : (AL, BL) ≠ (0, 0) := by
    intro hz
    apply hFn L
    rw [(hleft L le_rfl).eq_of_nhds, (hleft L le_rfl).deriv_eq,
      (hasDerivAt_seedConeLogHeight AL BL L).deriv]
    have hA : AL = 0 := congrArg Prod.fst hz
    have hB : BL = 0 := congrArg Prod.snd hz
    simp only [seedConeLogHeight, seedConeLogVelocity, hA, hB,
      mul_zero, zero_mul, add_zero, sub_zero]
  have hAR : (AR, BR) ≠ (0, 0) := by
    intro hz
    apply hFn R
    rw [(hright R le_rfl).eq_of_nhds, (hright R le_rfl).deriv_eq,
      (hasDerivAt_seedConeLogHeight AR BR R).deriv]
    have hA : AR = 0 := congrArg Prod.fst hz
    have hB : BR = 0 := congrArg Prod.snd hz
    simp only [seedConeLogHeight, seedConeLogVelocity, hA, hB,
      mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨⟨F, hFs, hF₀, hd₀, hFeq, hFn, AL, BL, AR, BR, hAL, hAR,
    fun y hy => (hleft y hy).eq_of_nhds,
    fun y hy => (hright y hy).eq_of_nhds⟩⟩

end ContinuousFlexibility.Radial
