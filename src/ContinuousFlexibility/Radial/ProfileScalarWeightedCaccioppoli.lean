module

public import ContinuousFlexibility.Radial.ProfileLayerCaccioppoli
public import ContinuousFlexibility.Radial.ProfileWeightedLayerIntegrals
public import ContinuousFlexibility.Radial.ProfileCellLayerEnergy
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Scalar weighted first-normal estimate

The actual endpoint-layer energy estimate is summed by layer index. A
fixed increase of the output coefficient exponent absorbs the profile
coefficient cost and the change of weights across each finite index
window. The same loss and constant work for every Fourier parameter and
every attenuation exponent in `[-1,1]`.
-/

@[expose] public section

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

namespace ContinuousFlexibility.Radial

theorem profile_scalar_weighted_caccioppoli
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (M₀ M₁ : ℝ) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 < K ∧
      ∀ (γ j : ℝ) (u f : ℝ → ℝ) (x₀ q : ℝ),
      |γ| ≤ 1 →
      ContDiffOn ℝ 1 u (radialCore D) →
      MemLp u 2 (volume.restrict (radialCore D)) →
      MemLp f 2 (volume.restrict (radialCore D)) →
      x₀ ∈ radialCore D →
      (∀ r ∈ radialCore D, D.w r * deriv u r =
        intervalLocalPrimitive
          (fun y => f y + j ^ 2 * (deriv D.w y / y) * u y) x₀ r + q) →
      Summable (fun m =>
        exp (2 * M₀ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D f m) →
      Summable (fun m =>
        exp (-2 * M₁ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D u m) →
      Summable (fun m =>
        exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m) ∧
      (∑' m,
        exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m) ≤
        K * ((∑' m,
          exp (2 * M₀ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D f m) +
          (1 + j ^ 2) * ∑' m,
            exp (-2 * M₁ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
              profileScalarCellSquare D u m) := by
  classical
  obtain ⟨C, h, hC⟩ := exists_accumulatingProfileBounds_one_le hD
  obtain ⟨A, T, hA, hT, henergy⟩ := profile_layer_caccioppoli_constants h (hC 0)
  obtain ⟨N, hN⟩ := profileEndpointLayer_index_window h
  have hpart : RadialPartition D := h.2.1
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  let M : ℝ := max M₁ (-M₀)
  have hMU : M₁ ≤ M := le_max_left _ _
  have hMF : -M₀ ≤ M := le_max_right _ _
  obtain ⟨L₀, K₀, hL₀, hK₀, hweight⟩ :=
    output_weight_absorb_on_index_window N (4 * T) M
  let L : ℝ := M - M₁ + L₀
  let H : ℝ := (B : ℝ) * K₀ * ((2 * N + 1 : ℕ) : ℝ)
  let P : ℝ := 7 * A ^ 4
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [hMU, hL₀]
  have hH : 0 ≤ H := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg B) hK₀.le) (Nat.cast_nonneg _)
  have hP : 0 ≤ P := mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hA) _)
  have hK : 0 < P * H + 1 := by linarith only [mul_nonneg hP hH]
  have hMnew : M₁ + L = M + L₀ := by dsimp only [L]; ring
  refine ⟨L, P * H + 1, hL, hK, ?_⟩
  intro γ j u f x₀ q hγ hu hu₂ hf hx₀ hflux hsF hsU
  let W : ℕ → ℝ := fun n => exp (-2 * (M₁ + L) * radialQ n + 2 * γ * radialS n)
  let E : ℕ → ℝ := fun n => exp (4 * T * radialQ n) * W n
  let WF : ℕ → ℝ := fun n => exp (2 * M₀ * radialQ n + 2 * γ * radialS n)
  let WU : ℕ → ℝ := fun n => exp (-2 * M₁ * radialQ n + 2 * γ * radialS n)
  let SF : ℝ := ∑' m, WF (D.cellIndex m) * profileScalarCellSquare D f m
  let SU : ℝ := ∑' m, WU (D.cellIndex m) * profileScalarCellSquare D u m
  have hW (n : ℕ) : 0 ≤ W n := (exp_pos _).le
  have hE (n : ℕ) : 0 ≤ E n := mul_nonneg (exp_pos _).le (hW n)
  have hWF (n : ℕ) : 0 ≤ WF n := (exp_pos _).le
  have hWU (n : ℕ) : 0 ≤ WU n := (exp_pos _).le
  have hweightF (n k : ℕ) (hnk : n ≤ k + N) (hkn : k ≤ n + N) :
      E n ≤ K₀ * WF k := by
    change exp (4 * T * radialQ n) *
      exp (-2 * (M₁ + L) * radialQ n + 2 * γ * radialS n) ≤
        K₀ * exp (2 * M₀ * radialQ k + 2 * γ * radialS k)
    rw [hMnew]
    apply (hweight γ hγ n k hnk hkn).trans
    apply mul_le_mul_of_nonneg_left _ hK₀.le
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hMF (radialQ_nonneg k)
    nlinarith only [hh]
  have hweightU (n k : ℕ) (hnk : n ≤ k + N) (hkn : k ≤ n + N) :
      E n ≤ K₀ * WU k := by
    change exp (4 * T * radialQ n) *
      exp (-2 * (M₁ + L) * radialQ n + 2 * γ * radialS n) ≤
        K₀ * exp (-2 * M₁ * radialQ k + 2 * γ * radialS k)
    rw [hMnew]
    apply (hweight γ hγ n k hnk hkn).trans
    apply mul_le_mul_of_nonneg_left _ hK₀.le
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hMU (radialQ_nonneg k)
    nlinarith only [hh]
  let Fint : ℕ → ℝ := fun n => ∫ r in profileEndpointLayer D (C 0) n, f r ^ 2
  let Uint : ℕ → ℝ := fun n => ∫ r in profileEndpointLayer D (C 0) n, u r ^ 2
  have hFsum (s : Finset ℕ) : (∑ n ∈ s, E n * Fint n) ≤ H * SF :=
    profile_weighted_layer_integrals_le h hN hB E WF hK₀.le hE hWF hweightF hf hsF s
  have hUsum (s : Finset ℕ) : (∑ n ∈ s, E n * Uint n) ≤ H * SU :=
    profile_weighted_layer_integrals_le h hN hB E WU hK₀.le hE hWU hweightU hu₂ hsU s
  have hSF : 0 ≤ SF := tsum_nonneg (fun m =>
    mul_nonneg (hWF _) (profileScalarCellSquare_nonneg D f m))
  have hSU : 0 ≤ SU := tsum_nonneg (fun m =>
    mul_nonneg (hWU _) (profileScalarCellSquare_nonneg D u m))
  have hJ : 0 ≤ 1 + j ^ 2 := by positivity
  have hR : 0 ≤ SF + (1 + j ^ 2) * SU := add_nonneg hSF (mul_nonneg hJ hSU)
  have hcut (n : ℕ) :
      W n * (∫ r in profileEndpointLayer D (C 0) n,
        profileLayerCutoff D (C 0) n r ^ 2 * deriv u r ^ 2) ≤
          P * (E n * (Fint n + (1 + j ^ 2) * Uint n)) := by
    have hb := mul_le_mul_of_nonneg_left
      (henergy j u f x₀ q hu hu₂ hf hx₀ hflux n) (hW n)
    calc
      _ ≤ W n * ((7 * A ^ 4) * exp (4 * T * radialQ n) *
          (Fint n + (1 + j ^ 2) * Uint n)) := hb
      _ = _ := by dsimp only [P, E]; ring
  have hfinite (s : Finset ℕ) :
      (∑ m ∈ s, W (D.cellIndex m) * profileScalarCellSquare D (deriv u) m) ≤
        (P * H + 1) * (SF + (1 + j ^ 2) * SU) := by
    let t : Finset ℕ := s.image D.cellIndex
    calc
      _ ≤ ∑ n ∈ t, W n * ∫ r in profileEndpointLayer D (C 0) n,
          profileLayerCutoff D (C 0) n r ^ 2 * deriv u r ^ 2 :=
        profile_cell_derivative_finset_le_layers h hu W hW s
      _ ≤ ∑ n ∈ t, P * (E n * (Fint n + (1 + j ^ 2) * Uint n)) :=
        Finset.sum_le_sum (fun n _ => hcut n)
      _ = P * ((∑ n ∈ t, E n * Fint n) +
          (1 + j ^ 2) * ∑ n ∈ t, E n * Uint n) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [mul_add, Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ P * (H * SF + (1 + j ^ 2) * (H * SU)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (hFsum t) (mul_le_mul_of_nonneg_left (hUsum t) hJ)) hP
      _ = (P * H) * (SF + (1 + j ^ 2) * SU) := by ring
      _ ≤ (P * H + 1) * (SF + (1 + j ^ 2) * SU) :=
        mul_le_mul_of_nonneg_right (by linarith) hR
  have hnonneg (m : ℕ) :
      0 ≤ W (D.cellIndex m) * profileScalarCellSquare D (deriv u) m :=
    mul_nonneg (hW _) (profileScalarCellSquare_nonneg D (deriv u) m)
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

end ContinuousFlexibility.Radial
