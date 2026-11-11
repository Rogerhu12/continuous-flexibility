import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The inner Poisson correction and its energy matrix

The lift `L` has the prescribed boundary values and residual `F`. Subtracting
the zero-boundary inverse `G F` constructs its homogeneous correction. The
Green identities below concern the lift and the inverse separately: neither
the Poisson equation nor the completed-square formula is an assumption.

The form space `V` and the source Hilbert space `H` are distinct. Thus `base`
can be the actual inclusion of a weighted form domain in its `L²` space,
including the scalar coordinate of a symmetric border. The final boundary
lemmas identify the energy matrix with actual conormal columns whenever a
trace and flux satisfy the full Green formula. The error estimate retains
one residual factor from each column, as in `eq:rad-eq-tm6` and
`eq:rad-eq-tm7` of the readable manuscript.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators InnerProductSpace

variable {ι V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual form identities for a lift and a zero-boundary inverse. -/
structure InnerPoissonGreenData (base : V →L[ℝ] H)
    (q : V →L[ℝ] V →L[ℝ] ℝ) (G : H →L[ℝ] V)
    (L : ι → V) (F : ι → H) (Z : Submodule ℝ V) : Prop where
  symmetric : ∀ u v, q u v = q v u
  solution_mem : ∀ f, G f ∈ Z
  lift_identity : ∀ i z, z ∈ Z → q (L i) z = ⟪F i, base z⟫_ℝ
  solution_identity : ∀ f z, z ∈ Z → q (G f) z = ⟪f, base z⟫_ℝ

/-- The corrected lift, with the original boundary values. -/
def innerPoissonLift (G : H →L[ℝ] V) (L : ι → V) (F : ι → H) (i : ι) : V :=
  L i - G (F i)

/-- The energy matrix of the constructed homogeneous columns. -/
def innerPoissonEnergyMatrix (q : V →L[ℝ] V →L[ℝ] ℝ)
    (G : H →L[ℝ] V) (L : ι → V) (F : ι → H) (i j : ι) : ℝ :=
  q (innerPoissonLift G L F i) (innerPoissonLift G L F j)

/-- The residual correction, using the actual source pairing. -/
def innerPoissonCorrectionMatrix (base : V →L[ℝ] H)
    (G : H →L[ℝ] V) (F : ι → H) (i j : ι) : ℝ :=
  ⟪F i, base (G (F j))⟫_ℝ

variable {base : V →L[ℝ] H} {q : V →L[ℝ] V →L[ℝ] ℝ}
  {G : H →L[ℝ] V} {L : ι → V} {F : ι → H} {Z : Submodule ℝ V}

/-- The residual cancels against the inverse on every zero-boundary test. -/
theorem innerPoissonLift_homogeneous (h : InnerPoissonGreenData base q G L F Z)
    (i : ι) (z : V) (hz : z ∈ Z) :
    q (innerPoissonLift G L F i) z = 0 := by
  rw [innerPoissonLift, map_sub, ContinuousLinearMap.sub_apply,
    h.lift_identity i z hz, h.solution_identity (F i) z hz, sub_self]

/-- A zero-boundary correction preserves every linear boundary trace. -/
theorem innerPoissonLift_trace (trace : V →ₗ[ℝ] (ι → ℝ))
    (htrace : ∀ f, trace (G f) = 0) (i : ι) :
    trace (innerPoissonLift G L F i) = trace (L i) := by
  rw [innerPoissonLift, map_sub, htrace, sub_zero]

theorem innerPoissonCorrectionMatrix_eq_form
    (h : InnerPoissonGreenData base q G L F Z) (i j : ι) :
    innerPoissonCorrectionMatrix base G F i j = q (G (F i)) (G (F j)) :=
  (h.solution_identity (F i) (G (F j)) (h.solution_mem (F j))).symm

/-- Symmetry of the inverse pairing follows from the symmetric actual form. -/
theorem innerPoissonCorrectionMatrix_symmetric
    (h : InnerPoissonGreenData base q G L F Z) (i j : ι) :
    innerPoissonCorrectionMatrix base G F i j =
      innerPoissonCorrectionMatrix base G F j i := by
  rw [innerPoissonCorrectionMatrix_eq_form h, innerPoissonCorrectionMatrix_eq_form h]
  exact h.symmetric _ _

/-- Completing the square removes exactly one inverse correction term. -/
theorem innerPoissonEnergyMatrix_eq (h : InnerPoissonGreenData base q G L F Z)
    (i j : ι) :
    innerPoissonEnergyMatrix q G L F i j =
      q (L i) (L j) - innerPoissonCorrectionMatrix base G F i j := by
  have horth : q (G (F i)) (innerPoissonLift G L F j) = 0 := by
    rw [h.symmetric]
    exact innerPoissonLift_homogeneous h j (G (F i)) (h.solution_mem (F i))
  calc
    innerPoissonEnergyMatrix q G L F i j =
        q (L i) (innerPoissonLift G L F j) -
          q (G (F i)) (innerPoissonLift G L F j) := by
      simp only [innerPoissonEnergyMatrix, innerPoissonLift, map_sub,
        ContinuousLinearMap.sub_apply]
    _ = q (L i) (innerPoissonLift G L F j) := by rw [horth, sub_zero]
    _ = q (L i) (L j) - innerPoissonCorrectionMatrix base G F i j := by
      rw [innerPoissonLift, map_sub, h.lift_identity i (G (F j))
        (h.solution_mem (F j))]
      rfl

theorem innerPoissonEnergyMatrix_symmetric
    (hsym : ∀ u v, q u v = q v u) (i j : ι) :
    innerPoissonEnergyMatrix q G L F i j = innerPoissonEnergyMatrix q G L F j i :=
  hsym _ _

/-- A lift estimate and an inverse estimate control the actual Poisson column. -/
theorem norm_base_innerPoissonLift_le (i : ι) :
    ‖base (innerPoissonLift G L F i)‖ ≤
      ‖base (L i)‖ + ‖base.comp G‖ * ‖F i‖ := by
  rw [innerPoissonLift, map_sub]
  refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
  simpa only [ContinuousLinearMap.comp_apply] using (base.comp G).le_opNorm (F i)

/-- Each correction entry contains one norm of each residual column. -/
theorem innerPoissonCorrectionMatrix_abs_le (R : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hG : ‖base.comp G‖ ≤ B) (hF : ∀ i, ‖F i‖ ≤ R i) (i j : ι) :
    |innerPoissonCorrectionMatrix base G F i j| ≤ B * R i * R j := by
  have hRi : 0 ≤ R i := (norm_nonneg _).trans (hF i)
  have hGj : ‖base (G (F j))‖ ≤ B * R j := by
    calc
      _ ≤ ‖base.comp G‖ * ‖F j‖ := by
        simpa only [ContinuousLinearMap.comp_apply] using (base.comp G).le_opNorm (F j)
      _ ≤ B * R j := mul_le_mul hG (hF j) (norm_nonneg _) hB
  calc
    |innerPoissonCorrectionMatrix base G F i j| ≤ ‖F i‖ * ‖base (G (F j))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ R i * (B * R j) := mul_le_mul (hF i) hGj (norm_nonneg _) hRi
    _ = B * R i * R j := by ring

/-- The error in the true energy matrix is the lift error plus a product
of two residual bounds. No positivity of the full shifted form is needed. -/
theorem innerPoissonEnergyMatrix_error_le [DecidableEq ι]
    (h : InnerPoissonGreenData base q G L F Z) (d R : ι → ℝ) {A B : ℝ}
    (hB : 0 ≤ B) (hG : ‖base.comp G‖ ≤ B) (hF : ∀ i, ‖F i‖ ≤ R i)
    (hL : ∀ i j, |q (L i) (L j) - (if i = j then d i else 0)| ≤ A * R i * R j)
    (i j : ι) :
    |innerPoissonEnergyMatrix q G L F i j - (if i = j then d i else 0)| ≤
      (A + B) * R i * R j := by
  rw [innerPoissonEnergyMatrix_eq h]
  calc
    |q (L i) (L j) - innerPoissonCorrectionMatrix base G F i j -
        (if i = j then d i else 0)| =
        |(q (L i) (L j) - (if i = j then d i else 0)) -
          innerPoissonCorrectionMatrix base G F i j| := by congr 1 <;> ring
    _ ≤ |q (L i) (L j) - (if i = j then d i else 0)| +
        |innerPoissonCorrectionMatrix base G F i j| := abs_sub _ _
    _ ≤ A * R i * R j + B * R i * R j :=
      add_le_add (hL i j) (innerPoissonCorrectionMatrix_abs_le R hB hG hF i j)
    _ = (A + B) * R i * R j := by ring

/-- Separate attenuations remain separate in every matrix entry. Taking
`a i = sqrt (d i)` gives the square-root energy factors of the manuscript. -/
theorem innerPoissonEnergyMatrix_two_attenuations [DecidableEq ι]
    (h : InnerPoissonGreenData base q G L F Z) (d a σ : ι → ℝ) {A B : ℝ}
    (hB : 0 ≤ B) (hG : ‖base.comp G‖ ≤ B)
    (hF : ∀ i, ‖F i‖ ≤ a i * Real.exp (-σ i))
    (hL : ∀ i j, |q (L i) (L j) - (if i = j then d i else 0)| ≤
      A * a i * a j * Real.exp (-σ i - σ j)) (i j : ι) :
    |innerPoissonEnergyMatrix q G L F i j - (if i = j then d i else 0)| ≤
      (A + B) * a i * a j * Real.exp (-σ i - σ j) := by
  have hprod (C : ℝ) (i j : ι) :
      C * (a i * Real.exp (-σ i)) * (a j * Real.exp (-σ j)) =
        C * a i * a j * Real.exp (-σ i - σ j) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have h := innerPoissonEnergyMatrix_error_le h d
    (fun i => a i * Real.exp (-σ i)) hB hG hF
    (fun i j => (hL i j).trans_eq (hprod A i j).symm) i j
  exact h.trans_eq (hprod (A + B) i j)

section Boundary

variable [Fintype ι] [DecidableEq ι]
  (trace flux : V →ₗ[ℝ] (ι → ℝ))

/-- The actual flux matrix; row `i` is the conormal at boundary point `i`. -/
def innerPoissonBoundaryMatrix (i j : ι) : ℝ :=
  flux (innerPoissonLift G L F j) i

/-- Subtracting the two full Green identities proves the homogeneous
Green identity, including its boundary terms. -/
theorem innerPoissonLift_boundary_green
    (hL : ∀ i v, q (L i) v = ⟪F i, base v⟫_ℝ +
      ∑ k, flux (L i) k * trace v k)
    (hG : ∀ f v, q (G f) v = ⟪f, base v⟫_ℝ +
      ∑ k, flux (G f) k * trace v k) (i : ι) (v : V) :
    q (innerPoissonLift G L F i) v =
      ∑ k, flux (innerPoissonLift G L F i) k * trace v k := by
  simp only [innerPoissonLift, map_sub, ContinuousLinearMap.sub_apply, Pi.sub_apply]
  rw [hL i v, hG (F i) v]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The energy matrix equals the true normalized conormal matrix. -/
theorem innerPoissonBoundaryMatrix_eq_energy
    (hsym : ∀ u v, q u v = q v u)
    (htraceG : ∀ f, trace (G f) = 0)
    (htraceL : ∀ i k, trace (L i) k = if i = k then 1 else 0)
    (hL : ∀ i v, q (L i) v = ⟪F i, base v⟫_ℝ +
      ∑ k, flux (L i) k * trace v k)
    (hG : ∀ f v, q (G f) v = ⟪f, base v⟫_ℝ +
      ∑ k, flux (G f) k * trace v k) (i j : ι) :
    innerPoissonBoundaryMatrix (G := G) (L := L) (F := F) flux i j =
      innerPoissonEnergyMatrix q G L F i j := by
  have ht (k : ι) : trace (innerPoissonLift G L F i) k = if i = k then 1 else 0 := by
    rw [innerPoissonLift_trace trace htraceG]
    exact htraceL i k
  calc
    innerPoissonBoundaryMatrix (G := G) (L := L) (F := F) flux i j =
        ∑ k, flux (innerPoissonLift G L F j) k *
          trace (innerPoissonLift G L F i) k := by
      simp only [innerPoissonBoundaryMatrix, ht]
      simp [eq_comm]
    _ = q (innerPoissonLift G L F j) (innerPoissonLift G L F i) :=
      (innerPoissonLift_boundary_green trace flux hL hG j _).symm
    _ = innerPoissonEnergyMatrix q G L F i j := hsym _ _

/-- Full Green formulas supply the zero-boundary hypotheses used above. -/
theorem innerPoissonGreenData_of_boundary_green
    (hsym : ∀ u v, q u v = q v u)
    (htraceG : ∀ f, trace (G f) = 0)
    (hL : ∀ i v, q (L i) v = ⟪F i, base v⟫_ℝ +
      ∑ k, flux (L i) k * trace v k)
    (hG : ∀ f v, q (G f) v = ⟪f, base v⟫_ℝ +
      ∑ k, flux (G f) k * trace v k) :
    InnerPoissonGreenData base q G L F (LinearMap.ker trace) := by
  refine ⟨hsym, fun f => LinearMap.mem_ker.mpr (htraceG f), ?_, ?_⟩
  · intro i z hz
    have hz0 : trace z = 0 := LinearMap.mem_ker.mp hz
    simpa only [hz0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] using hL i z
  · intro f z hz
    have hz0 : trace z = 0 := LinearMap.mem_ker.mp hz
    simpa only [hz0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] using hG f z

/-- The full Green formula identifies the true boundary matrix with
`energy(L,L) - F*G F`, rather than defining the flux by that identity. -/
theorem innerPoissonBoundaryMatrix_eq
    (hsym : ∀ u v, q u v = q v u)
    (htraceG : ∀ f, trace (G f) = 0)
    (htraceL : ∀ i k, trace (L i) k = if i = k then 1 else 0)
    (hL : ∀ i v, q (L i) v = ⟪F i, base v⟫_ℝ +
      ∑ k, flux (L i) k * trace v k)
    (hG : ∀ f v, q (G f) v = ⟪f, base v⟫_ℝ +
      ∑ k, flux (G f) k * trace v k) (i j : ι) :
    innerPoissonBoundaryMatrix (G := G) (L := L) (F := F) flux i j =
      q (L i) (L j) - innerPoissonCorrectionMatrix base G F i j := by
  rw [innerPoissonBoundaryMatrix_eq_energy trace flux hsym htraceG htraceL hL hG]
  exact innerPoissonEnergyMatrix_eq
    (innerPoissonGreenData_of_boundary_green trace flux hsym htraceG hL hG) i j

theorem innerPoissonBoundaryMatrix_symmetric
    (hsym : ∀ u v, q u v = q v u)
    (htraceG : ∀ f, trace (G f) = 0)
    (htraceL : ∀ i k, trace (L i) k = if i = k then 1 else 0)
    (hL : ∀ i v, q (L i) v = ⟪F i, base v⟫_ℝ +
      ∑ k, flux (L i) k * trace v k)
    (hG : ∀ f v, q (G f) v = ⟪f, base v⟫_ℝ +
      ∑ k, flux (G f) k * trace v k) (i j : ι) :
    innerPoissonBoundaryMatrix (G := G) (L := L) (F := F) flux i j =
      innerPoissonBoundaryMatrix (G := G) (L := L) (F := F) flux j i := by
  rw [innerPoissonBoundaryMatrix_eq_energy trace flux hsym htraceG htraceL hL hG,
    innerPoissonBoundaryMatrix_eq_energy trace flux hsym htraceG htraceL hL hG]
  exact innerPoissonEnergyMatrix_symmetric hsym i j

end Boundary

end ContinuousFlexibility.Radial
