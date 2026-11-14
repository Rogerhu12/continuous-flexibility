module

public import ContinuousFlexibility.Radial.OuterFirstOrderState
public import ContinuousFlexibility.Radial.MorseChainLocalGluing
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuing every actual core state into the deep tail

A left Dirichlet solution and a normalized natural solution span the state
space at the deep entrance.  The finite-interval ODE therefore determines
an actual continuation of every initial core state.  The existing physical
gluing operation is C¹ because both value and flux match, including the
derivative at the interface itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

/-- Matching values identify the existing glued function on the closed right side. -/
theorem morseGlueCut_eq_right_of_matching {c x : ℝ} {f g : ℝ → ℝ}
    (hmatch : f c = g c) (hx : c ≤ x) : morseGlueCut c f g x = g x := by
  by_cases hxc : x ≤ c
  · have he : x = c := le_antisymm hxc hx
    subst x
    simpa only [morseGlueCut, le_refl, ite_true] using hmatch
  · simp only [morseGlueCut, hxc, ite_false]

/-- Matching first derivatives give a genuine derivative at the join. -/
theorem hasDerivAt_morseGlueCut_of_matching {c d : ℝ} {f g : ℝ → ℝ}
    (hmatch : f c = g c) (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) :
    HasDerivAt (morseGlueCut c f g) d c := by
  have hL : HasDerivWithinAt (morseGlueCut c f g) d (Iic c) c :=
    hf.hasDerivWithinAt.congr_of_mem
      (fun x hx => by
        change x ≤ c at hx
        simp only [morseGlueCut, hx, ite_true]) (by simp only [mem_Iic, le_refl])
  have hR : HasDerivWithinAt (morseGlueCut c f g) d (Ici c) c :=
    hg.hasDerivWithinAt.congr_of_mem
      (fun x hx => morseGlueCut_eq_right_of_matching hmatch (mem_Ici.mp hx))
      (by simp only [mem_Ici, le_refl])
  have h := hL.union hR
  have hu : Iic c ∪ Ici c = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x c
  rw [hu] at h
  exact h.hasDerivAt (by simp)

/-- The original value/flux system survives the actual core/tail gluing. -/
theorem outerFirstOrderSystem_glue {a b c : ℝ} {alpha beta uL zL uR zR : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c < b)
    (hL : OuterFirstOrderSystem alpha beta uL zL (Icc a c))
    (hR : OuterFirstOrderSystem alpha beta uR zR (Ico c b))
    (hmatch : (uL c, zL c) = (uR c, zR c)) :
    OuterFirstOrderSystem alpha beta (morseGlueCut c uL uR)
      (morseGlueCut c zL zR) (Ico a b) := by
  have hu : uL c = uR c := congrArg Prod.fst hmatch
  have hz : zL c = zR c := congrArg Prod.snd hmatch
  intro x hx
  rcases lt_trichotomy x c with hxc | he | hcx
  · have hxl : x ∈ Icc a c := ⟨hx.1, hxc.le⟩
    have hug : morseGlueCut c uL uR =ᶠ[𝓝 x] uL := by
      filter_upwards [Iio_mem_nhds hxc] with y hy
      change y < c at hy
      simp only [morseGlueCut, hy.le, ite_true]
    have hzg : morseGlueCut c zL zR =ᶠ[𝓝 x] zL := by
      filter_upwards [Iio_mem_nhds hxc] with y hy
      change y < c at hy
      simp only [morseGlueCut, hy.le, ite_true]
    simpa only [morseGlueCut, hxc.le, ite_true] using
      ⟨(hL x hxl).1.congr_of_eventuallyEq hug, (hL x hxl).2.congr_of_eventuallyEq hzg⟩
  · subst x
    have hcl : c ∈ Icc a c := ⟨hac, le_rfl⟩
    have hcr : c ∈ Ico c b := ⟨le_rfl, hcb⟩
    have hdu := hasDerivAt_morseGlueCut_of_matching hu (hL c hcl).1
      ((hR c hcr).1.congr_deriv (by rw [hz]))
    have hdz := hasDerivAt_morseGlueCut_of_matching hz (hL c hcl).2
      ((hR c hcr).2.congr_deriv (by rw [hu]))
    simpa only [morseGlueCut, le_refl, ite_true] using ⟨hdu, hdz⟩
  · have hxr : x ∈ Ico c b := ⟨hcx.le, hx.2⟩
    have hug : morseGlueCut c uL uR =ᶠ[𝓝 x] uR := by
      filter_upwards [Ioi_mem_nhds hcx] with y hy
      change c < y at hy
      simp only [morseGlueCut, not_le_of_gt hy, ite_false]
    have hzg : morseGlueCut c zL zR =ᶠ[𝓝 x] zR := by
      filter_upwards [Ioi_mem_nhds hcx] with y hy
      change c < y at hy
      simp only [morseGlueCut, not_le_of_gt hy, ite_false]
    simpa only [morseGlueCut, not_le_of_gt hcx, ite_false] using
      ⟨(hR x hxr).1.congr_of_eventuallyEq hug, (hR x hxr).2.congr_of_eventuallyEq hzg⟩

theorem OuterFirstOrderSystem.const_mul {alpha beta u z : ℝ → ℝ} {s : Set ℝ}
    (h : OuterFirstOrderSystem alpha beta u z s) (C : ℝ) :
    OuterFirstOrderSystem alpha beta (fun x => C * u x) (fun x => C * z x) s := by
  intro x hx
  exact ⟨((h x hx).1.const_mul C).congr_deriv (by ring),
    ((h x hx).2.const_mul C).congr_deriv (by ring)⟩

theorem OuterFirstOrderSystem.linear_combination {alpha beta u z v q : ℝ → ℝ} {s : Set ℝ}
    (hU : OuterFirstOrderSystem alpha beta u z s)
    (hV : OuterFirstOrderSystem alpha beta v q s) (A B : ℝ) :
    OuterFirstOrderSystem alpha beta (fun x => A * u x + B * v x)
      (fun x => A * z x + B * q x) s := by
  intro x hx
  exact ⟨(((hU x hx).1.const_mul A).add ((hV x hx).1.const_mul B)).congr_deriv (by ring),
    (((hU x hx).2.const_mul A).add ((hV x hx).2.const_mul B)).congr_deriv (by ring)⟩

/-- The determinant of two actual full states is constant on every convex interval. -/
theorem outerFirstOrderSystem_state_determinant {alpha beta u z v q : ℝ → ℝ}
    {s : Set ℝ} (hs : Convex ℝ s)
    (hU : OuterFirstOrderSystem alpha beta u z s)
    (hV : OuterFirstOrderSystem alpha beta v q s)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    u y * q y - z y * v y = u x * q x - z x * v x := by
  have hd : ∀ t ∈ s, HasDerivAt (fun r => u r * q r - z r * v r) 0 t := by
    intro t ht
    exact (((hU t ht).1.mul (hV t ht).2).sub
      ((hU t ht).2.mul (hV t ht).1)).congr_deriv (by ring)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun _ _ => by simp) hs hx hy
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hb

/-- Every initial full state has an actual continuation through the finite
core and along the entire deep tail.  The only division is by the nonzero
flux of the deep Dirichlet basis at its own entrance. -/
theorem exists_outer_continued_state {a b c : ℝ} (hac : a ≤ c) (hcb : c < b)
    {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (halpha : ContinuousOn alpha (Icc a c)) (hbeta : ContinuousOn beta (Icc a c))
    (hP : OuterFirstOrderSystem alpha beta P ZP (Ico c b))
    (hQ : OuterFirstOrderSystem alpha beta Q ZQ (Ico c b))
    (hPc : P c = 1) (hQc : Q c = 0) (hZQc : ZQ c ≠ 0) (v : ℝ × ℝ) :
    ∃ u z : ℝ → ℝ, ∃ A B : ℝ,
      (u a, z a) = v ∧ OuterFirstOrderSystem alpha beta u z (Ico a b) ∧
      (∀ x ∈ Ico c b, u x = A * P x + B * Q x) ∧
      (∀ x ∈ Ico c b, z x = A * ZP x + B * ZQ x) := by
  obtain ⟨uL, zL, hinit, hL⟩ := exists_outerFirstOrder_state hac halpha hbeta a v
  let A : ℝ := uL c
  let B : ℝ := (zL c - A * ZP c) / ZQ c
  let uR : ℝ → ℝ := fun x => A * P x + B * Q x
  let zR : ℝ → ℝ := fun x => A * ZP x + B * ZQ x
  have hR : OuterFirstOrderSystem alpha beta uR zR (Ico c b) :=
    hP.linear_combination hQ A B
  have hu : uL c = uR c := by
    dsimp only [uR, A]
    rw [hPc, hQc, mul_one, mul_zero, add_zero]
  have hz : zL c = zR c := by
    dsimp only [zR, B]
    rw [div_mul_cancel₀ _ hZQc]
    ring
  refine ⟨morseGlueCut c uL uR, morseGlueCut c zL zR, A, B, ?_,
    outerFirstOrderSystem_glue hac hcb hL hR (Prod.ext hu hz), ?_, ?_⟩
  · simpa only [morseGlueCut, hac, ite_true] using hinit
  · intro x hx
    exact morseGlueCut_eq_right_of_matching hu hx.1
  · intro x hx
    exact morseGlueCut_eq_right_of_matching hz hx.1

end ContinuousFlexibility.Radial
