import ContinuousFlexibility.Radial.TailNaturalInterpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# From actual classical tail solutions to their node recurrence

Wronskians of continuous states are constant on a closed edge when the
first-order equations hold in its interior. This includes an edge touching
the entrance, where the original density need only be smooth from the right.
The canonical Poisson pair has nonzero Wronskian, so its two endpoint values
determine every classical solution on that edge.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

/-- Interior equations and endpoint continuity suffice for closed-edge Wronskian conservation. -/
theorem tailFirstOrderSystem_wronskian_const_Icc
    {p u v U V : ℝ → ℝ} {Λ a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hU : ContinuousOn U (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (h : TailFirstOrderSystem p Λ u v (Ioo a b))
    (h' : TailFirstOrderSystem p Λ U V (Ioo a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    tailFirstOrderWronskian u v U V x = tailFirstOrderWronskian u v U V a := by
  have hc : ContinuousOn (tailFirstOrderWronskian u v U V) (Icc a b) :=
    (hu.mul hV).sub (hv.mul hU)
  have hd := tailFirstOrderSystem_hasDerivAt_wronskian h h'
  rcases lt_or_eq_of_le hx.1 with hax | hax
  · have hdiff : DifferentiableOn ℝ (tailFirstOrderWronskian u v U V) (Ioo a x) :=
      fun y hy => (hd y ⟨hy.1, hy.2.trans_le hx.2⟩).differentiableAt.differentiableWithinAt
    obtain ⟨y, hy, hm⟩ := exists_deriv_eq_slope (tailFirstOrderWronskian u v U V) hax
      (hc.mono (Icc_subset_Icc_right hx.2)) hdiff
    rw [(hd y ⟨hy.1, hy.2.trans_le hx.2⟩).deriv] at hm
    have hz := (eq_div_iff (sub_pos.mpr hax).ne').mp hm
    linarith only [hz]
  · rw [← hax]

private theorem tail_two_wronskians_injective {u v U V f₀ g₀ f₁ g₁ : ℝ}
    (hdet : f₀ * g₁ - g₀ * f₁ ≠ 0)
    (h₀ : u * g₀ - v * f₀ = U * g₀ - V * f₀)
    (h₁ : u * g₁ - v * f₁ = U * g₁ - V * f₁) : u = U ∧ v = V := by
  have hz₀ : (u - U) * g₀ - (v - V) * f₀ = 0 := by nlinarith only [h₀]
  have hz₁ : (u - U) * g₁ - (v - V) * f₁ = 0 := by nlinarith only [h₁]
  have hmu : (u - U) * (f₀ * g₁ - g₀ * f₁) = 0 := by
    calc
      _ = f₀ * ((u - U) * g₁ - (v - V) * f₁) -
          f₁ * ((u - U) * g₀ - (v - V) * f₀) := by ring
      _ = 0 := by rw [hz₀, hz₁]; ring
  have hmv : (v - V) * (f₀ * g₁ - g₀ * f₁) = 0 := by
    calc
      _ = g₀ * ((u - U) * g₁ - (v - V) * f₁) -
          g₁ * ((u - U) * g₀ - (v - V) * f₀) := by ring
      _ = 0 := by rw [hz₀, hz₁]; ring
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hmu).resolve_right hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hmv).resolve_right hdet)⟩

theorem tailActualEdgeInterpolation_system {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) :
    TailFirstOrderSystem T.p T.Λ (tailActualEdgeInterpolation T hT n a b)
      (tailActualEdgeInterpolationFlux T hT n a b) (Icc (T.node n) (T.node (n + 1))) :=
  fun _ hx => ⟨tailActualEdgeInterpolation_hasDerivAt hT n a b hx,
    tailActualEdgeInterpolationFlux_hasDerivAt hT n a b hx⟩

theorem tailActualEdgeInterpolationFlux_continuousOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) :
    ContinuousOn (tailActualEdgeInterpolationFlux T hT n a b)
      (Icc (T.node n) (T.node (n + 1))) :=
  HasDerivAt.continuousOn (fun _ hx => tailActualEdgeInterpolationFlux_hasDerivAt hT n a b hx)

/-- The two actual Poisson columns have Wronskian equal to their positive coupling. -/
theorem tailActualEdgeInterpolation_wronskian {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    tailFirstOrderWronskian (tailActualEdgeInterpolation T hT n 1 0)
      (tailActualEdgeInterpolationFlux T hT n 1 0) (tailActualEdgeInterpolation T hT n 0 1)
      (tailActualEdgeInterpolationFlux T hT n 0 1) x = tailActualNodeCoupling T hT n := by
  have h := tailFirstOrderSystem_wronskian_const_Icc
    (tailActualEdgeInterpolation_differentiable hT n 1 0).continuous.continuousOn
    (tailActualEdgeInterpolationFlux_continuousOn hT n 1 0)
    (tailActualEdgeInterpolation_differentiable hT n 0 1).continuous.continuousOn
    (tailActualEdgeInterpolationFlux_continuousOn hT n 0 1)
    ((tailActualEdgeInterpolation_system hT n 1 0).mono Ioo_subset_Icc_self)
    ((tailActualEdgeInterpolation_system hT n 0 1).mono Ioo_subset_Icc_self) hx
  rw [h]
  rw [tailFirstOrderWronskian, (tailActualEdgeInterpolation_endpoints hT n 1 0).1,
    (tailActualEdgeInterpolation_endpoints hT n 0 1).1,
    (tailActualEdgeInterpolationFlux_endpoints hT n 0 1).1]
  ring

/-- Every continuous classical state has the canonical two-endpoint flux formula. -/
theorem tailActualEdge_solution_flux_endpoints {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (T.node n) (T.node (n + 1))))
    (hv : ContinuousOn v (Icc (T.node n) (T.node (n + 1))))
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node n) (T.node (n + 1)))) :
    v (T.node n) =
        -tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) false * u (T.node n) +
          tailActualNodeCoupling T hT n * u (T.node (n + 1)) ∧
      v (T.node (n + 1)) =
        -tailActualNodeCoupling T hT n * u (T.node n) +
          tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) true * u (T.node (n + 1)) := by
  have hw (a b : ℝ) := tailFirstOrderSystem_wronskian_const_Icc hu hv
    (tailActualEdgeInterpolation_differentiable hT n a b).continuous.continuousOn
    (tailActualEdgeInterpolationFlux_continuousOn hT n a b) hsys
    ((tailActualEdgeInterpolation_system hT n a b).mono Ioo_subset_Icc_self)
    (show T.node (n + 1) ∈ Icc (T.node n) (T.node (n + 1)) from
      ⟨(tailActualEdge_order hT n).le, le_rfl⟩)
  have hrel (a b : ℝ) :
      u (T.node (n + 1)) * (-tailActualNodeCoupling T hT n * a +
          tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) true * b) -
        v (T.node (n + 1)) * b =
      u (T.node n) * (-tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) false * a +
          tailActualNodeCoupling T hT n * b) - v (T.node n) * a := by
    simpa only [tailFirstOrderWronskian,
      (tailActualEdgeInterpolation_endpoints hT n a b).1,
      (tailActualEdgeInterpolation_endpoints hT n a b).2,
      (tailActualEdgeInterpolationFlux_endpoints hT n a b).1,
      (tailActualEdgeInterpolationFlux_endpoints hT n a b).2] using hw a b
  constructor
  · nlinarith only [hrel 1 0]
  · nlinarith only [hrel 0 1]

/-- Initial value and flux determine a continuous classical state on the whole closed edge. -/
theorem tailActualEdge_state_eq_of_initial {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) {u v U V : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (T.node n) (T.node (n + 1))))
    (hv : ContinuousOn v (Icc (T.node n) (T.node (n + 1))))
    (hU : ContinuousOn U (Icc (T.node n) (T.node (n + 1))))
    (hV : ContinuousOn V (Icc (T.node n) (T.node (n + 1))))
    (h : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node n) (T.node (n + 1))))
    (h' : TailFirstOrderSystem T.p T.Λ U V (Ioo (T.node n) (T.node (n + 1))))
    (hu₀ : u (T.node n) = U (T.node n)) (hv₀ : v (T.node n) = V (T.node n))
    {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) : u x = U x ∧ v x = V x := by
  have hw (a b : ℝ) :
      tailFirstOrderWronskian u v (tailActualEdgeInterpolation T hT n a b)
          (tailActualEdgeInterpolationFlux T hT n a b) x =
        tailFirstOrderWronskian U V (tailActualEdgeInterpolation T hT n a b)
          (tailActualEdgeInterpolationFlux T hT n a b) x := by
    have hc : ContinuousOn (tailActualEdgeInterpolation T hT n a b)
        (Icc (T.node n) (T.node (n + 1))) :=
      (tailActualEdgeInterpolation_differentiable hT n a b).continuous.continuousOn
    have hf := tailActualEdgeInterpolationFlux_continuousOn hT n a b
    have hs := (tailActualEdgeInterpolation_system hT n a b).mono Ioo_subset_Icc_self
    rw [tailFirstOrderSystem_wronskian_const_Icc hu hv hc hf h hs hx,
      tailFirstOrderSystem_wronskian_const_Icc hU hV hc hf h' hs hx]
    dsimp only [tailFirstOrderWronskian]
    rw [hu₀, hv₀]
  have hd : tailFirstOrderWronskian (tailActualEdgeInterpolation T hT n 1 0)
      (tailActualEdgeInterpolationFlux T hT n 1 0) (tailActualEdgeInterpolation T hT n 0 1)
      (tailActualEdgeInterpolationFlux T hT n 0 1) x ≠ 0 := by
    rw [tailActualEdgeInterpolation_wronskian hT n hx]
    exact (tailActualNodeCoupling_pos hT n).ne'
  exact tail_two_wronskians_injective hd (hw 1 0) (hw 0 1)

/-- Every actual classical solution is its same-endpoint canonical interpolation. -/
theorem tailActualEdge_solution_eq_interpolation {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (T.node n) (T.node (n + 1))))
    (hv : ContinuousOn v (Icc (T.node n) (T.node (n + 1))))
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node n) (T.node (n + 1))))
    {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    u x = tailActualEdgeInterpolation T hT n (u (T.node n)) (u (T.node (n + 1))) x ∧
      v x = tailActualEdgeInterpolationFlux T hT n (u (T.node n)) (u (T.node (n + 1))) x := by
  apply tailActualEdge_state_eq_of_initial hT n hu hv
    (tailActualEdgeInterpolation_differentiable hT n (u (T.node n))
      (u (T.node (n + 1)))).continuous.continuousOn
    (tailActualEdgeInterpolationFlux_continuousOn hT n (u (T.node n)) (u (T.node (n + 1)))) hsys
    ((tailActualEdgeInterpolation_system hT n (u (T.node n))
      (u (T.node (n + 1)))).mono Ioo_subset_Icc_self) ?_ ?_ hx
  · exact (tailActualEdgeInterpolation_endpoints hT n (u (T.node n)) (u (T.node (n + 1)))).1.symm
  · rw [(tailActualEdgeInterpolationFlux_endpoints hT n (u (T.node n)) (u (T.node (n + 1)))).1]
    exact (tailActualEdge_solution_flux_endpoints hT n hu hv hsys).1

theorem tailActualEdge_subset_outward {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    Icc (T.node n) (T.node (n + 1)) ⊆ Ico (T.node 0) T.endpoint :=
  fun _ hx => ⟨((deepTail_node_strictMono hT).monotone (Nat.zero_le n)).trans hx.1,
    hx.2.trans_lt (deepTail_node_lt_endpoint hT (n + 1))⟩

theorem tailActualEdge_interior_subset_outward {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    Ioo (T.node n) (T.node (n + 1)) ⊆ Ioo (T.node 0) T.endpoint :=
  fun _ hx => ⟨((deepTail_node_strictMono hT).monotone (Nat.zero_le n)).trans_lt hx.1,
    hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩

/-- The actual classical solution induces the physical node recurrence, before any node summability. -/
theorem tailActualSolution_node_recurrence {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Ico (T.node 0) T.endpoint))
    (hv : ContinuousOn v (Ico (T.node 0) T.endpoint))
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node 0) T.endpoint)) (n : ℕ) :
    -tailActualInteriorDiagonal T hT n * u (T.node (n + 1)) =
      tailActualNodeCoupling T hT n * u (T.node n) +
        tailActualNodeCoupling T hT (n + 1) * u (T.node (n + 2)) := by
  have hflux (k : ℕ) := tailActualEdge_solution_flux_endpoints hT k
    (hu.mono (tailActualEdge_subset_outward hT k)) (hv.mono (tailActualEdge_subset_outward hT k))
    (hsys.mono (tailActualEdge_interior_subset_outward hT k))
  have hL := (hflux n).2
  have hR := (hflux (n + 1)).1
  dsimp only [tailActualInteriorDiagonal]
  nlinarith only [hL, hR]

end ContinuousFlexibility.Radial
