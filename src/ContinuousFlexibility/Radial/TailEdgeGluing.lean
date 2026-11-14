module

public import ContinuousFlexibility.Radial.MorseChainLocalGluing
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gluing actual tail solutions by matching value and flux

The existing half-open outward gluing operation also applies when adjacent
pieces have matching values and first derivatives, without requiring equality
of their germs outside the edge. At a node the two closed-edge derivatives
combine to give the derivative on a full neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

/-- The existing gluing continues its first piece inward, so it has that
piece's full germ at the first node. No matching assumption is needed here. -/
theorem tailOutwardGlue_first_germ {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono enter) :
    morseOutwardGlue enter piece =ᶠ[𝓝 (enter 0)] piece 0 := by
  filter_upwards [Iio_mem_nhds (hmono (Nat.lt_succ_self 0))] with x hx
  by_cases h : x < enter 0
  · simp only [morseOutwardGlue, ite_eq_left h]
  · exact morseOutwardGlue_apply_block hmono ⟨le_of_not_gt h, hx⟩

/-- Matching endpoint values make the half-open gluing equal to each piece
on its whole closed edge. -/
theorem tailOutwardGlue_apply_closed {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono enter)
    (hmatch : ∀ n, piece n (enter (n + 1)) = piece (n + 1) (enter (n + 1)))
    {n : ℕ} {x : ℝ} (hx : x ∈ Icc (enter n) (enter (n + 1))) :
    morseOutwardGlue enter piece x = piece n x := by
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · exact morseOutwardGlue_apply_block hmono ⟨hx.1, hlt⟩
  · rw [morseOutwardGlue_apply_block hmono
      (show enter (n + 1) ∈ Ico (enter (n + 1)) (enter (n + 1 + 1)) from
        ⟨le_rfl, hmono (Nat.lt_succ_self (n + 1))⟩)]
    exact (hmatch n).symm

/-- Derivatives on one closed edge transfer to the actual glued function. -/
theorem tailOutwardGlue_hasDerivWithinAt {enter : ℕ → ℝ}
    {piece slope : ℕ → ℝ → ℝ} (hmono : StrictMono enter)
    (hmatch : ∀ n, piece n (enter (n + 1)) = piece (n + 1) (enter (n + 1)))
    (hderiv : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      HasDerivAt (piece n) (slope n x) x)
    {n : ℕ} {x : ℝ} (hx : x ∈ Icc (enter n) (enter (n + 1))) :
    HasDerivWithinAt (morseOutwardGlue enter piece) (slope n x)
      (Icc (enter n) (enter (n + 1))) x :=
  (hderiv n x hx).hasDerivWithinAt.congr_of_mem
    (fun y hy => tailOutwardGlue_apply_closed hmono hmatch hy) hx

/-- A matching first derivative gives a genuine derivative at every point
strictly between the first node and the accumulation endpoint. -/
theorem tailOutwardGlue_hasDerivAt {enter : ℕ → ℝ} {endpoint : ℝ}
    {piece slope : ℕ → ℝ → ℝ} (hmono : StrictMono enter)
    (hlim : Tendsto enter atTop (𝓝 endpoint))
    (hmatch : ∀ n, piece n (enter (n + 1)) = piece (n + 1) (enter (n + 1)))
    (hslope : ∀ n, slope n (enter (n + 1)) = slope (n + 1) (enter (n + 1)))
    (hderiv : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      HasDerivAt (piece n) (slope n x) x)
    {x : ℝ} (hx : x ∈ Ioo (enter 0) endpoint) :
    HasDerivAt (morseOutwardGlue enter piece) (morseOutwardGlue enter slope x) x := by
  obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1.le hx.2
  have hnc : x ∈ Icc (enter n) (enter (n + 1)) := ⟨hn.1, hn.2.le⟩
  rw [tailOutwardGlue_apply_closed hmono hslope hnc]
  rcases lt_or_eq_of_le hn.1 with hlt | heq
  · exact (tailOutwardGlue_hasDerivWithinAt hmono hmatch hderiv hnc).hasDerivAt
      (Icc_mem_nhds hlt hn.2)
  · subst x
    cases n with
    | zero => exact (lt_irrefl _ hx.1).elim
    | succ n =>
      have hn₀ : enter n < enter (n + 1) := hmono (Nat.lt_succ_self n)
      have hn₁ : enter (n + 1) < enter (n + 1 + 1) :=
        hmono (Nat.lt_succ_self (n + 1))
      have hL := tailOutwardGlue_hasDerivWithinAt hmono hmatch hderiv
        (show enter (n + 1) ∈ Icc (enter n) (enter (n + 1)) from ⟨hn₀.le, le_rfl⟩)
      rw [hslope n] at hL
      have hR := tailOutwardGlue_hasDerivWithinAt hmono hmatch hderiv
        (show enter (n + 1) ∈ Icc (enter (n + 1)) (enter (n + 1 + 1)) from
          ⟨le_rfl, hn₁.le⟩)
      have hU := hL.union hR
      rw [Icc_union_Icc_eq_Icc hn₀.le hn₁.le] at hU
      exact hU.hasDerivAt (Icc_mem_nhds hn₀ hn₁)

/-- The same derivative statement includes the first node, using the
first piece's full germ there. -/
theorem tailOutwardGlue_hasDerivAt_Ico {enter : ℕ → ℝ} {endpoint : ℝ}
    {piece slope : ℕ → ℝ → ℝ} (hmono : StrictMono enter)
    (hlim : Tendsto enter atTop (𝓝 endpoint))
    (hmatch : ∀ n, piece n (enter (n + 1)) = piece (n + 1) (enter (n + 1)))
    (hslope : ∀ n, slope n (enter (n + 1)) = slope (n + 1) (enter (n + 1)))
    (hderiv : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      HasDerivAt (piece n) (slope n x) x)
    {x : ℝ} (hx : x ∈ Ico (enter 0) endpoint) :
    HasDerivAt (morseOutwardGlue enter piece) (morseOutwardGlue enter slope x) x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hlt
  · rw [morseOutwardGlue_apply_block hmono
      (show enter 0 ∈ Ico (enter 0) (enter (0 + 1)) from
        ⟨le_rfl, hmono (Nat.lt_succ_self 0)⟩)]
    exact (hderiv 0 _ ⟨le_rfl, (hmono (Nat.lt_succ_self 0)).le⟩).congr_of_eventuallyEq
      (tailOutwardGlue_first_germ hmono)
  · exact tailOutwardGlue_hasDerivAt hmono hlim hmatch hslope hderiv ⟨hlt, hx.2⟩

theorem tailOutwardGlue_continuousOn {enter : ℕ → ℝ} {endpoint : ℝ}
    {piece slope : ℕ → ℝ → ℝ} (hmono : StrictMono enter)
    (hlim : Tendsto enter atTop (𝓝 endpoint))
    (hmatch : ∀ n, piece n (enter (n + 1)) = piece (n + 1) (enter (n + 1)))
    (hslope : ∀ n, slope n (enter (n + 1)) = slope (n + 1) (enter (n + 1)))
    (hderiv : ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      HasDerivAt (piece n) (slope n x) x) :
    ContinuousOn (morseOutwardGlue enter piece) (Ioo (enter 0) endpoint) :=
  fun _ hx => (tailOutwardGlue_hasDerivAt hmono hlim hmatch hslope hderiv hx).continuousAt.continuousWithinAt

end ContinuousFlexibility.Radial
