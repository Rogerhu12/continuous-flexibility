module

public import ContinuousFlexibility.Radial.HermiteCompleteness
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A genuine Hermite Hilbert basis of actual `L²`

The vectors are the already constructed normalized real Hermite--Gaussian
functions, inserted into Lebesgue `Lp`. Integral orthonormality and the
proved totality theorem supply the two hypotheses of the Hilbert-basis
constructor. Its coefficients are then identified with actual integrals.
No closed differential-operator domain is introduced here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

abbrev HermiteL2 : Type := Lp ℝ 2 (volume : Measure ℝ)

/-- The actual normalized function, considered as an `L²` equivalence class. -/
def hermiteL2Vector {j : ℝ} (hj : 0 < j) (n : ℕ) : HermiteL2 :=
  MemLp.toLp (normalizedOscillatorHermite j n)
    (normalizedOscillatorHermite_energyDomain hj n).2.1

theorem hermiteL2Vector_coeFn {j : ℝ} (hj : 0 < j) (n : ℕ) :
    (hermiteL2Vector hj n : ℝ → ℝ) =ᵐ[volume] normalizedOscillatorHermite j n :=
  MemLp.coeFn_toLp (normalizedOscillatorHermite_energyDomain hj n).2.1

theorem hermiteL2Vector_inner {j : ℝ} (hj : 0 < j) (m n : ℕ) :
    ⟪hermiteL2Vector hj m, hermiteL2Vector hj n⟫_ℝ = if m = n then 1 else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x : ℝ, normalizedOscillatorHermite j m x * normalizedOscillatorHermite j n x := by
      apply integral_congr_ae
      filter_upwards [hermiteL2Vector_coeFn hj m, hermiteL2Vector_coeFn hj n] with x hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := integral_normalizedOscillatorHermite_mul hj m n

theorem hermiteL2Vector_orthonormal {j : ℝ} (hj : 0 < j) :
    Orthonormal ℝ (hermiteL2Vector hj) :=
  orthonormal_iff_ite.mpr (hermiteL2Vector_inner hj)

/-- Coefficients are genuine `dX` Lebesgue integral pairings. -/
def hermiteCoefficient (j : ℝ) (u : HermiteL2) (n : ℕ) : ℝ :=
  ∫ x : ℝ, u x * normalizedOscillatorHermite j n x

theorem hermiteCoefficient_integrable {j : ℝ} (hj : 0 < j) (u : HermiteL2) (n : ℕ) :
    Integrable (fun x : ℝ => u x * normalizedOscillatorHermite j n x) volume :=
  (Lp.memLp u).integrable_mul (normalizedOscillatorHermite_energyDomain hj n).2.1

theorem inner_hermiteL2Vector_left {j : ℝ} (hj : 0 < j) (u : HermiteL2) (n : ℕ) :
    ⟪hermiteL2Vector hj n, u⟫_ℝ = hermiteCoefficient j u n := by
  rw [L2.inner_def]
  unfold hermiteCoefficient
  apply integral_congr_ae
  filter_upwards [hermiteL2Vector_coeFn hj n] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]

theorem inner_hermiteL2Vector_right {j : ℝ} (hj : 0 < j) (u : HermiteL2) (n : ℕ) :
    ⟪u, hermiteL2Vector hj n⟫_ℝ = hermiteCoefficient j u n := by
  calc
    _ = ⟪hermiteL2Vector hj n, u⟫_ℝ := real_inner_comm _ _
    _ = _ := inner_hermiteL2Vector_left hj u n

/-- The orthogonal complement is zero by the proved completeness theorem
for actual `Lp` classes, not by an added completeness premise. -/
theorem hermiteL2Vector_span_orthogonal {j : ℝ} (hj : 0 < j) :
    (Submodule.span ℝ (Set.range (hermiteL2Vector hj)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  rw [Submodule.mem_bot]
  apply normalizedHermite_complete_Lp hj u
  intro n
  have hn : hermiteL2Vector hj n ∈ Submodule.span ℝ (Set.range (hermiteL2Vector hj)) :=
    Submodule.subset_span ⟨n, rfl⟩
  have hz := (Submodule.mem_orthogonal _ u).mp hu (hermiteL2Vector hj n) hn
  rw [inner_hermiteL2Vector_left hj] at hz
  exact hz

/-- A Hilbert basis in the actual Lebesgue `L²` Hilbert space. -/
def hermiteBasis {j : ℝ} (hj : 0 < j) : HilbertBasis ℕ ℝ HermiteL2 :=
  HilbertBasis.mkOfOrthogonalEqBot (hermiteL2Vector_orthonormal hj)
    (hermiteL2Vector_span_orthogonal hj)

@[simp] theorem hermiteBasis_apply {j : ℝ} (hj : 0 < j) (n : ℕ) :
    hermiteBasis hj n = hermiteL2Vector hj n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (hermiteL2Vector_orthonormal hj) (hermiteL2Vector_span_orthogonal hj)) n

theorem hermiteBasis_coeFn {j : ℝ} (hj : 0 < j) (n : ℕ) :
    (hermiteBasis hj n : ℝ → ℝ) =ᵐ[volume] normalizedOscillatorHermite j n := by
  rw [hermiteBasis_apply]
  exact hermiteL2Vector_coeFn hj n

theorem hermiteBasis_repr_eq_coefficient {j : ℝ} (hj : 0 < j) (u : HermiteL2) (n : ℕ) :
    (hermiteBasis hj).repr u n = hermiteCoefficient j u n := by
  rw [(hermiteBasis hj).repr_apply_apply, hermiteBasis_apply, inner_hermiteL2Vector_left hj]

/-- The coefficient map is an isometric equivalence from actual Lebesgue
`L²` to square-summable real sequences. -/
def hermiteCoefficientTransform {j : ℝ} (hj : 0 < j) :
    HermiteL2 ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  (hermiteBasis hj).repr

theorem hermiteCoefficientTransform_apply {j : ℝ} (hj : 0 < j)
    (u : HermiteL2) (n : ℕ) :
    hermiteCoefficientTransform hj u n = hermiteCoefficient j u n :=
  hermiteBasis_repr_eq_coefficient hj u n

theorem hermiteCoefficientTransform_norm {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    ‖hermiteCoefficientTransform hj u‖ = ‖u‖ :=
  (hermiteCoefficientTransform hj).norm_map u

/-- Every actual square-summable sequence is realized by the Hermite series. -/
theorem hermiteSynthesis_hasSum {j : ℝ} (hj : 0 < j)
    (c : lp (fun _ : ℕ => ℝ) 2) :
    HasSum (fun n => c n • hermiteL2Vector hj n)
      ((hermiteCoefficientTransform hj).symm c) := by
  simpa only [hermiteCoefficientTransform, hermiteBasis_apply] using
    (hermiteBasis hj).hasSum_repr_symm c

/-- The actual Hermite expansion converges in the `L²` norm topology. -/
theorem hermiteExpansion_hasSum {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    HasSum (fun n => hermiteCoefficient j u n • hermiteL2Vector hj n) u := by
  simpa only [hermiteBasis_repr_eq_coefficient hj, hermiteBasis_apply] using
    (hermiteBasis hj).hasSum_repr u

theorem hermiteExpansion_tsum {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    (∑' n : ℕ, hermiteCoefficient j u n • hermiteL2Vector hj n) = u :=
  (hermiteExpansion_hasSum hj u).tsum_eq

theorem hermiteExpansion_partialSums {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      hermiteCoefficient j u n • hermiteL2Vector hj n) atTop (𝓝 u) :=
  (hermiteExpansion_hasSum hj u).tendsto_sum_nat

theorem hermiteL2Vector_dense_span {j : ℝ} (hj : 0 < j) :
    (Submodule.span ℝ (Set.range (hermiteL2Vector hj))).topologicalClosure = ⊤ := by
  have heq : ⇑(hermiteBasis hj) = hermiteL2Vector hj :=
    funext (hermiteBasis_apply hj)
  simpa only [heq] using (hermiteBasis hj).dense_span

/-- Parseval with the actual Lebesgue-integral coefficients. -/
theorem hermiteCoefficient_hasSum_sq {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    HasSum (fun n => hermiteCoefficient j u n ^ 2) (‖u‖ ^ 2) := by
  simpa only [hermiteBasis_apply, inner_hermiteL2Vector_right hj,
    inner_hermiteL2Vector_left hj, pow_two, real_inner_self_eq_norm_sq] using
    (hermiteBasis hj).hasSum_inner_mul_inner u u

theorem hermiteCoefficient_summable_sq {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    Summable (fun n => hermiteCoefficient j u n ^ 2) :=
  (hermiteCoefficient_hasSum_sq hj u).summable

theorem hermiteCoefficient_parseval {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    (∑' n : ℕ, hermiteCoefficient j u n ^ 2) = ‖u‖ ^ 2 :=
  (hermiteCoefficient_hasSum_sq hj u).tsum_eq

theorem hermiteCoefficient_hasSum_mul {j : ℝ} (hj : 0 < j) (u v : HermiteL2) :
    HasSum (fun n => hermiteCoefficient j u n * hermiteCoefficient j v n)
      ⟪u, v⟫_ℝ := by
  simpa only [hermiteBasis_apply, inner_hermiteL2Vector_right hj,
    inner_hermiteL2Vector_left hj] using (hermiteBasis hj).hasSum_inner_mul_inner u v

/-- The bilinear Parseval identity is an identity of actual `dX` integrals. -/
theorem hermiteCoefficient_parseval_integral {j : ℝ} (hj : 0 < j) (u v : HermiteL2) :
    (∑' n : ℕ, hermiteCoefficient j u n * hermiteCoefficient j v n) =
      ∫ x : ℝ, u x * v x := by
  calc
    _ = ⟪u, v⟫_ℝ := (hermiteCoefficient_hasSum_mul hj u v).tsum_eq
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [RCLike.inner_apply, conj_trivial]
      ring

theorem hermiteCoefficient_parseval_integral_sq {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    (∑' n : ℕ, hermiteCoefficient j u n ^ 2) = ∫ x : ℝ, u x ^ 2 := by
  simpa only [pow_two] using hermiteCoefficient_parseval_integral hj u u

end ContinuousFlexibility.Radial
