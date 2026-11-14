import ContinuousFlexibility.Analysis.N01cOpticalMaterialBounds

/-!
# Affine square-root jets on a closed spatial set

The existing optical-root product and envelope estimates also apply at
the two endpoints of a closed physical half. Here the scalar inputs are
globally smooth, while positivity and numerical bounds are required only
on the displayed set. The actual directional tower is identified with
the existing affine optical tower. No extension of a quantitative bound
to an exterior collar is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04NegativeChart_affineSqrtJet_material_bounds
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : Seminorm ℝ X) {U : Set X} (hU : IsOpen U)
    (I : ι → Set ℝ) (q₀ g : ι → ℝ → ℝ) (L : ι → X →L[ℝ] ℝ)
    (hq : ∀ m, ContDiff ℝ ∞ (q₀ m)) (hg : ∀ m, ContDiff ℝ ∞ (g m))
    (E H : ι → ℝ) (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    {R c₀ K : ℝ} (hR : 0 < R) (hHR : ∀ m, H m ≤ R)
    (hc₀ : 0 < c₀) (hK : 0 < K)
    (hlower : ∀ m r, r ∈ I m → ∀ x ∈ U,
      c₀ * E m ^ (-K) ≤ q₀ m r + L m x * g m r)
    (hjetq : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ x ∈ U,
        |iteratedDeriv j (fun s => q₀ m s + L m x * g m s) r| ≤ C * E m ^ A)
    (hjetg : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v : X,
        |iteratedDeriv j (fun s => L m v * g m s) r| ≤ C * E m ^ A * H m * p v)
    (n k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ m r, r ∈ I m →
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n
        (fun s => Real.sqrt (q₀ m s + L m x * g m s)) r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        |J.D k x v| ≤ C * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i) := by
  classical
  choose cq aq hcq haq hbq using hjetq
  choose cg ag hcg hag hbg using hjetg
  let A : ℕ → ι → ℝ := fun j m => cq j * E m ^ aq j
  let B : ℕ → ι → ℝ := fun j m => cg j * E m ^ ag j
  let c : ι → ℝ := fun m => c₀ * E m ^ (-K)
  have hc (m) : 0 < c m :=
    mul_pos hc₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hE m)) _)
  have hA₀ (j m) : 0 ≤ A j m :=
    mul_nonneg (hcq j).le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  have hB₀ (j m) : 0 ≤ B j m :=
    mul_nonneg (hcg j).le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  have hAe (j) : HasPositiveEnvelope E (A j) :=
    ⟨cq j, aq j, hcq j, haq j, fun _ => le_rfl⟩
  have hBe (j) : HasPositiveEnvelope E (B j) :=
    ⟨cg j, ag j, hcg j, hag j, fun _ => le_rfl⟩
  have hci : HasPositiveEnvelope E (fun m => (c m)⁻¹) :=
    hasPositiveEnvelope_inv_of_lower hE hc₀ hK (fun _ => le_rfl)
  have hupper (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) :
      q₀ m r + L m x * g m r ≤ A 0 m := by
    have hb := hbq 0 m r hr x hx
    exact (le_abs_self _).trans (by simpa only [iteratedDeriv_zero] using hb)
  have hpos (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) :
      0 < q₀ m r + L m x * g m r := (hc m).trans_le (hlower m r hr x hx)
  by_cases hk : k = 0
  · subst k
    obtain ⟨C, D, hC, hD, henvelope⟩ :=
      endpointPowerCompositionMajorant_envelope E c (A 0) A hE hc
        (hA₀ 0) hA₀ hci (hAe 0) hAe 0 n
    refine ⟨C, D, hC, hD, fun m r hr J x hx v => ?_⟩
    rw [smoothDirections_D_zero_apply J hx v]
    simp only [parameterHeightWeight, ite_true, Fin.prod_univ_zero, mul_one]
    have hQ : ContDiffAt ℝ ∞ (fun s => q₀ m s + L m x * g m s) r :=
      (hq m).contDiffAt.add (contDiffAt_const.mul (hg m).contDiffAt)
    have hb := endpoint_sqrt_radial_bound (δ := (1 : ℝ)) hQ zero_lt_one
      (hc m) (hA₀ 0 m)
      (by simpa only [mul_one] using hlower m r hr x hx)
      (by simpa only [mul_one] using hupper m r hr x hx)
      (fun j => A j m) (fun j => hA₀ j m) n
      (fun j _ => by simpa only [one_pow, one_mul] using hbq j m r hr x hx)
    have hb' : |iteratedDeriv n (fun s => Real.sqrt (q₀ m s + L m x * g m s)) r| ≤
        endpointPowerCompositionMajorant (c m) (A 0 m) (fun j => A j m) 0 n := by
      simpa only [one_pow, one_mul, Real.sqrt_one] using hb
    exact hb'.trans (henvelope m)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have he := endpointRootProductMajorant_envelope E c (A 0) A B hE hc
      (hA₀ 0) hA₀ hB₀ hci (hAe 0) hAe hBe k n
    let d : ℝ := |rpowJetCoefficient (1 / 2) k| * R ^ (k - 1)
    obtain ⟨C, D, hC, hD, henvelope⟩ :=
      (hasPositiveEnvelope_const E hE d).mul hE he
        (fun m => endpointRootProductMajorant_nonneg (hc m).le _ _
          (fun j => hA₀ j m) (fun j => hB₀ j m) k n)
    refine ⟨C, D, hC, hD, fun m r hr J x hx v => ?_⟩
    let Jcan := affineOpticalRadialJetSmoothDirections (L m) isOpen_univ
      (hq m).contDiffOn (hg m).contDiffOn n r (mem_univ r) hU (hpos m r hr)
    have heq : J.D k x v = Jcan.D k x v := congrArg
      (fun Q : X [×k]→L[ℝ] ℝ => Q v)
      (HasProjectiveJetsOn.unique hU J.hasProjectiveJetsOn Jcan.hasProjectiveJetsOn k x hx)
    rw [heq]
    have hb := affineOpticalRadialJetSmoothDirections_endpoint_bound
      (δ := (1 : ℝ)) (L m) isOpen_univ (hq m).contDiffOn (hg m).contDiffOn
      n k hkpos r (mem_univ r) hU (hpos m r hr) hx v zero_lt_one (hc m) (hA₀ 0 m)
      (by simpa only [mul_one] using hlower m r hr x hx)
      (by simpa only [mul_one] using hupper m r hr x hx)
      (fun j => A j m) (fun j => B j m) (fun j => hA₀ j m) (fun j => hB₀ j m)
      (fun i => p (v i)) (fun i => apply_nonneg _ _) (hH m) (hHR m)
      (fun j _ => by simpa only [one_pow, one_mul] using hbq j m r hr x hx)
      (fun i j _ => by simpa only [one_pow, one_mul] using hbg j m r hr (v i))
    have hb' : |Jcan.D k x v| ≤
        (d * endpointRootProductMajorant (c m) (A 0 m)
          (fun j => A j m) (fun j => B j m) k n) * H m * ∏ i, p (v i) := by
      simpa only [one_pow, one_mul, Real.sqrt_one, mul_one, d,
        mul_assoc, mul_left_comm, mul_comm] using hb
    exact hb'.trans (by
      simp only [parameterHeightWeight, if_neg hk]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (henvelope m) (hH m))
        (Finset.prod_nonneg (fun i _ => apply_nonneg p _)))

end ContinuousFlexibility.Analysis
