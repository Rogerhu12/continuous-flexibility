import ContinuousFlexibility.Analysis.N07bNormalizedSourceJetBounds
import ContinuousFlexibility.Analysis.N07bNormalizedDirectionChain

/-!
# Finite jets for layer-dependent normalized directions

The geometric direction and drift may change at every layer. Retaining
the invariant j+n<=b gives the same finite constant and degree as for one
fixed direction. The actual normalized paths satisfy this recurrence by
the preceding genuine material-coordinate differentiation identities.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Each layer may use its own two direction fields and drift. Primitive
jets are required only in the finite triangle `k + n <= b`. -/
theorem n07b_threeBranch_layered_jets_le
    {U : Set PolarPoint} (hU : IsOpen U)
    {a : (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ}
    {v₁ v₂ q : ℕ → PolarPoint → ℝ}
    (ha : ∀ j i, ContDiffOn ℝ ∞ (a j i) U)
    (hv₁ : ∀ k, ContDiffOn ℝ ∞ (v₁ k) U)
    (hv₂ : ∀ k, ContDiffOn ℝ ∞ (v₂ k) U) (hq : ∀ k, ContDiffOn ℝ ∞ (q k) U)
    (hstay : ∀ j i, EqOn (a (j + 1) (i, 0))
      (fun y => v₁ j y * radialPartial (a j i) y + v₂ j y * angularPartial (a j i) y + q j y * a j i y) U)
    (hradial : ∀ j i, EqOn (a (j + 1) (i, 1)) (fun y => v₁ j y * a j i y) U)
    (hangular : ∀ j i, EqOn (a (j + 1) (i, 2)) (fun y => v₂ j y * a j i y) U)
    {x : PolarPoint} (hx : x ∈ U) (b : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (a 0 ()) x‖ ≤ R)
    (hv₁jet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (v₁ k) x‖ ≤ R)
    (hv₂jet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (v₂ k) x‖ ≤ R)
    (hqjet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (q k) x‖ ≤ R) :
    ∀ j (i : n07bAngularChainIndex j) (n : ℕ), j + n ≤ b →
      ‖iteratedFDeriv ℝ n (a j i) x‖ ≤ n07bSourceChainJetConstant b ^ j * R ^ (j + 1) := by
  have hP : 0 ≤ n07bFiniteJetProductConstant b := zero_le_one.trans (one_le_n07bFiniteJetProductConstant b)
  have hK : 0 ≤ n07bSourceChainJetConstant b := zero_le_one.trans (one_le_n07bSourceChainJetConstant b)
  intro j
  induction j with
  | zero =>
      intro i n hn
      cases i
      simpa only [zero_add, pow_zero, pow_one, one_mul] using
        hinit n (by simpa only [zero_add] using hn)
  | succ j ih =>
      rintro ⟨i, k⟩ n hn
      have hnB : n ≤ b := by omega
      let D : ℝ := n07bSourceChainJetConstant b ^ j * R ^ (j + 1)
      let L : ℝ := n07bFiniteJetProductConstant b * R * D
      have hD : 0 ≤ D := mul_nonneg (pow_nonneg hK _) (pow_nonneg hR _)
      have hL : 0 ≤ L := mul_nonneg (mul_nonneg hP hR) hD
      have hajet (t : ℕ) (ht : t ≤ n + 1) : ‖iteratedFDeriv ℝ t (a j i) x‖ ≤ D :=
        ih i t (by omega)
      have hrad : ContDiffOn ℝ ∞ (radialPartial (a j i)) U := by
        intro y hy
        exact (contDiffAt_radialPartial ((ha j i).contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
      have hang : ContDiffOn ℝ ∞ (angularPartial (a j i)) U := by
        intro y hy
        exact (contDiffAt_angularPartial ((ha j i).contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
      have hmul {v g : PolarPoint → ℝ}
          (hv : ContDiffOn ℝ ∞ v U) (hg : ContDiffOn ℝ ∞ g U)
          (hvj : ∀ t : ℕ, t ≤ n → ‖iteratedFDeriv ℝ t v x‖ ≤ R)
          (hgj : ∀ t : ℕ, t ≤ n → ‖iteratedFDeriv ℝ t g x‖ ≤ D) :
          ‖iteratedFDeriv ℝ n (fun y => v y * g y) x‖ ≤ L :=
        n07b_norm_jet_mul_le hU hv hg hx hR hD hvj hgj hnB
      let g₁ : PolarPoint → ℝ := fun y => v₁ j y * radialPartial (a j i) y
      let g₂ : PolarPoint → ℝ := fun y => v₂ j y * angularPartial (a j i) y
      let g₃ : PolarPoint → ℝ := fun y => q j y * a j i y
      have hg₁ : ContDiffOn ℝ ∞ g₁ U := (hv₁ j).mul hrad
      have hg₂ : ContDiffOn ℝ ∞ g₂ U := (hv₂ j).mul hang
      have hg₃ : ContDiffOn ℝ ∞ g₃ U := (hq j).mul (ha j i)
      have h₁ : ‖iteratedFDeriv ℝ n g₁ x‖ ≤ L := hmul (hv₁ j) hrad
        (fun t ht => hv₁jet j t (by omega))
        (fun t ht => (n07b_norm_jet_radialPartial_le hU (ha j i) hx t).trans
          (hajet (t + 1) (by omega)))
      have h₂ : ‖iteratedFDeriv ℝ n g₂ x‖ ≤ L := hmul (hv₂ j) hang
        (fun t ht => hv₂jet j t (by omega))
        (fun t ht => (n07b_norm_jet_angularPartial_le hU (ha j i) hx t).trans
          (hajet (t + 1) (by omega)))
      have h₃ : ‖iteratedFDeriv ℝ n g₃ x‖ ≤ L := hmul (hq j) (ha j i)
        (fun t ht => hqjet j t (by omega)) (fun t ht => hajet t (by omega))
      have hstep : 3 * L = n07bSourceChainJetConstant b ^ (j + 1) * R ^ (j + 1 + 1) := by
        dsimp only [L, D]
        simp only [pow_succ]
        unfold n07bSourceChainJetConstant
        ring
      fin_cases k
      · have heq : a (j + 1) (i, 0) =ᶠ[𝓝 x] (fun y => g₁ y + g₂ y + g₃ y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hstay j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ (‖iteratedFDeriv ℝ n g₁ x‖ + ‖iteratedFDeriv ℝ n g₂ x‖) +
              ‖iteratedFDeriv ℝ n g₃ x‖ :=
            (n07b_norm_jet_add_le hU (hg₁.add hg₂) hg₃ hx n).trans
              (add_le_add (n07b_norm_jet_add_le hU hg₁ hg₂ hx n) le_rfl)
          _ ≤ L + L + L := add_le_add (add_le_add h₁ h₂) h₃
          _ = 3 * L := by ring
          _ = _ := hstep
      · have heq : a (j + 1) (i, 1) =ᶠ[𝓝 x] (fun y => v₁ j y * a j i y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hradial j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ L := hmul (hv₁ j) (ha j i) (fun t ht => hv₁jet j t (by omega))
            (fun t ht => hajet t (by omega))
          _ ≤ 3 * L := by linarith
          _ = _ := hstep
      · have heq : a (j + 1) (i, 2) =ᶠ[𝓝 x] (fun y => v₂ j y * a j i y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hangular j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ L := hmul (hv₂ j) (ha j i) (fun t ht => hv₂jet j t (by omega))
            (fun t ht => hajet t (by omega))
          _ ≤ 3 * L := by linarith
          _ = _ := hstep

/-- A common finite-order bound for all paths of the layered recurrence. -/
theorem n07b_threeBranch_layered_value_le
    {U : Set PolarPoint} (hU : IsOpen U)
    {a : (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ}
    {v₁ v₂ q : ℕ → PolarPoint → ℝ}
    (ha : ∀ j i, ContDiffOn ℝ ∞ (a j i) U)
    (hv₁ : ∀ k, ContDiffOn ℝ ∞ (v₁ k) U)
    (hv₂ : ∀ k, ContDiffOn ℝ ∞ (v₂ k) U) (hq : ∀ k, ContDiffOn ℝ ∞ (q k) U)
    (hstay : ∀ j i, EqOn (a (j + 1) (i, 0))
      (fun y => v₁ j y * radialPartial (a j i) y + v₂ j y * angularPartial (a j i) y + q j y * a j i y) U)
    (hradial : ∀ j i, EqOn (a (j + 1) (i, 1)) (fun y => v₁ j y * a j i y) U)
    (hangular : ∀ j i, EqOn (a (j + 1) (i, 2)) (fun y => v₂ j y * a j i y) U)
    {x : PolarPoint} (hx : x ∈ U) (b : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (a 0 ()) x‖ ≤ R)
    (hv₁jet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (v₁ k) x‖ ≤ R)
    (hv₂jet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (v₂ k) x‖ ≤ R)
    (hqjet : ∀ k n : ℕ, k + n ≤ b → ‖iteratedFDeriv ℝ n (q k) x‖ ≤ R)
    {j : ℕ} (hj : j ≤ b) (i : n07bAngularChainIndex j) :
    |a j i x| ≤ n07bSourceChainJetConstant b ^ b * R ^ (b + 1) := by
  have hR0 := zero_le_one.trans hR
  have hK := one_le_n07bSourceChainJetConstant b
  have h := n07b_threeBranch_layered_jets_le hU ha hv₁ hv₂ hq hstay hradial hangular hx b hR0
    hinit hv₁jet hv₂jet hqjet j i 0 (by simpa using hj)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul
    (pow_le_pow_right₀ hK hj) (pow_le_pow_right₀ hR (Nat.add_le_add_right hj 1))
    (pow_nonneg hR0 _) (pow_nonneg (zero_le_one.trans hK) _))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- The actual coefficients of a word of geometric directions satisfy
the layered estimate. Their derivative identities are conclusions of the
real chart calculus in the preceding module, not extra hypotheses here. -/
theorem n07b_normalizedDirectionChain_jets_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    (hX : ∀ k, ContDiffOn ℝ ∞ (X k) (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    {y : PolarPoint} (hy : y ∈ n07bSourceMaterialPiece T K z m) (b : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c 0 ()) y‖ ≤ R)
    (hv₁jet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV1 T (X k)) y‖ ≤ R)
    (hv₂jet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV2 T (X k)) y‖ ≤ R)
    (hqjet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionDrift T K z m (X k)) y‖ ≤ R) :
    ∀ j (i : n07bAngularChainIndex j) (n : ℕ), j + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i) y‖ ≤
        n07bSourceChainJetConstant b ^ j * R ^ (j + 1) := by
  have hfields (k : ℕ) := n07b_materialDirectionFields_contDiffOn hT hK hz hs m (hX k)
  exact n07b_threeBranch_layered_jets_le (n07bSourceMaterialPiece_isOpen hT hK hz hs m)
    (n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn hD hT hK hz hs m β hX hc)
    (fun k => (hfields k).1) (fun k => (hfields k).2.1) (fun k => (hfields k).2.2)
    (fun j i y hy => n07bMaterialNormalizedDirectionChainCoefficient_stay
      hD hT hK hz hs m β hX hc j i hy)
    (fun j i y _ => n07bMaterialNormalizedDirectionChainCoefficient_radial T K z m β X c j i y)
    (fun j i y _ => n07bMaterialNormalizedDirectionChainCoefficient_angular T K z m β X c j i y)
    hy b hR hinit hv₁jet hv₂jet hqjet

/-- The uniform finite-order path value bound for the same actual word. -/
theorem n07b_normalizedDirectionChain_value_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    (hX : ∀ k, ContDiffOn ℝ ∞ (X k) (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    {y : PolarPoint} (hy : y ∈ n07bSourceMaterialPiece T K z m) (b : ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c 0 ()) y‖ ≤ R)
    (hv₁jet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV1 T (X k)) y‖ ≤ R)
    (hv₂jet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV2 T (X k)) y‖ ≤ R)
    (hqjet : ∀ k n : ℕ, k + n ≤ b →
      ‖iteratedFDeriv ℝ n (n07bMaterialDirectionDrift T K z m (X k)) y‖ ≤ R)
    {j : ℕ} (hj : j ≤ b) (i : n07bAngularChainIndex j) :
    |n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i y| ≤
      n07bSourceChainJetConstant b ^ b * R ^ (b + 1) := by
  have hR0 := zero_le_one.trans hR
  have hK0 := one_le_n07bSourceChainJetConstant b
  have h := n07b_normalizedDirectionChain_jets_le hD hT hK hz hs m β hX hc hy b hR0
    hinit hv₁jet hv₂jet hqjet j i 0 (by simpa using hj)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul
    (pow_le_pow_right₀ hK0 hj) (pow_le_pow_right₀ hR (Nat.add_le_add_right hj 1))
    (pow_nonneg hR0 _) (pow_nonneg (zero_le_one.trans hK0) _))

end ContinuousFlexibility.Analysis
