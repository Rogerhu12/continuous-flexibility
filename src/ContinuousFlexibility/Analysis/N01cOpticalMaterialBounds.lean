module

public import ContinuousFlexibility.Analysis.N01cOpticalNumericEnvelopes
public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra
public import ContinuousFlexibility.Analysis.N01cCommonType

/-!
# Material bounds for the genuine optical-root parameter towers

The numerical input estimates are the affine optical square and its
actual linear directions. Their endpoint powers are cancelled before
the finite scalar coefficients are absorbed into the material envelope.
The parameter set and the controlling seminorm do not depend on either
derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Actual affine optical-root jets, uniformly in an arbitrary component
index. The assumptions estimate only the square and its linear inputs. -/
theorem affineOpticalRadialJet_material_bounds
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : Seminorm ℝ X) {U : Set X} (hU : IsOpen U)
    (I : ι → Set ℝ) (hI : ∀ m, IsOpen (I m))
    (q₀ g : ι → ℝ → ℝ) (L : ι → X →L[ℝ] ℝ)
    (hq : ∀ m, ContDiffOn ℝ ∞ (q₀ m) (I m))
    (hg : ∀ m, ContDiffOn ℝ ∞ (g m) (I m))
    (δ : ι → ℝ → ℝ) (E H : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    {width R c₀ K : ℝ} (hwidth : 0 < width) (hR : 0 < R)
    (hHR : ∀ m, H m ≤ R) (hc₀ : 0 < c₀) (hK : 0 < K)
    (hδ : ∀ m r, r ∈ I m → 0 < δ m r ∧ δ m r ≤ width)
    (hlower : ∀ m r, r ∈ I m → ∀ x ∈ U,
      c₀ * E m ^ (-K) * δ m r ≤ q₀ m r + L m x * g m r)
    (hjetq : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ x ∈ U,
        δ m r ^ j * |iteratedDeriv j (fun s => q₀ m s + L m x * g m s) r| ≤
          C * E m ^ A * δ m r)
    (hjetg : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v : X,
        δ m r ^ j * |iteratedDeriv j (fun s => L m v * g m s) r| ≤
          C * E m ^ A * δ m r * H m * p v)
    (n k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I m),
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n
        (fun s => Real.sqrt (q₀ m s + L m x * g m s)) r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * |J.D k x v| ≤
          C * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i) := by
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
      q₀ m r + L m x * g m r ≤ A 0 m * δ m r := by
    have hh := hbq 0 m r hr x hx
    have habs : |q₀ m r + L m x * g m r| ≤ A 0 m * δ m r := by
      simpa only [A, pow_zero, one_mul, iteratedDeriv_zero] using hh
    exact (le_abs_self _).trans habs
  have hpos (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) :
      0 < q₀ m r + L m x * g m r :=
    (mul_pos (hc m) (hδ m r hr).1).trans_le (hlower m r hr x hx)
  have hqjet (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) (j) :
      δ m r ^ j * |iteratedDeriv j (fun s => q₀ m s + L m x * g m s) r| ≤
        δ m r * A j m := by
    simpa only [A, mul_comm] using hbq j m r hr x hx
  have hgjet (m r) (hr : r ∈ I m) (v : X) (j) :
      δ m r ^ j * |iteratedDeriv j (fun s => L m v * g m s) r| ≤
        δ m r * B j m * H m * p v := by
    simpa only [B, mul_assoc, mul_left_comm, mul_comm] using hbg j m r hr v
  by_cases hk : k = 0
  · subst k
    have he := endpointPowerCompositionMajorant_envelope E c (A 0) A hE hc
      (hA₀ 0) hA₀ hci (hAe 0) hAe 0 n
    have hfull := (hasPositiveEnvelope_const E hE (Real.sqrt width)).mul hE he
      (fun m => endpointPowerCompositionMajorant_nonneg (hc m).le _
        (fun j => hA₀ j m) 0 n)
    obtain ⟨C, D, hC, hD, henvelope⟩ := hfull
    refine ⟨C, D, hC, hD, fun m r hr J x hx v => ?_⟩
    rw [smoothDirections_D_zero_apply J hx v]
    simp only [parameterHeightWeight, ite_true, Fin.prod_univ_zero, mul_one]
    have hQ : ContDiffAt ℝ ∞ (fun s => q₀ m s + L m x * g m s) r :=
      ((hq m).contDiffAt ((hI m).mem_nhds hr)).add
        (contDiffAt_const.mul ((hg m).contDiffAt ((hI m).mem_nhds hr)))
    have hb := endpoint_sqrt_radial_bound hQ (hδ m r hr).1 (hc m) (hA₀ 0 m)
      (hlower m r hr x hx) (hupper m r hr x hx) (fun j => A j m)
      (fun j => hA₀ j m) n (fun j _ => hqjet m r hr x hx j)
    exact hb.trans ((mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (hδ m r hr).2)
      (endpointPowerCompositionMajorant_nonneg (hc m).le _ (fun j => hA₀ j m) 0 n)).trans
        (henvelope m))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have he := endpointRootProductMajorant_envelope E c (A 0) A B hE hc
      (hA₀ 0) hA₀ hB₀ hci (hAe 0) hAe hBe k n
    let d : ℝ := |rpowJetCoefficient (1 / 2) k| * Real.sqrt width * R ^ (k - 1)
    have hd : 0 ≤ d := mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (pow_nonneg hR.le _)
    have hfull := (hasPositiveEnvelope_const E hE d).mul hE he
      (fun m => endpointRootProductMajorant_nonneg (hc m).le _ _
        (fun j => hA₀ j m) (fun j => hB₀ j m) k n)
    obtain ⟨C, D, hC, hD, henvelope⟩ := hfull
    refine ⟨C, D, hC, hD, fun m r hr J x hx v => ?_⟩
    let Jcan := affineOpticalRadialJetSmoothDirections (L m) (hI m) (hq m) (hg m)
      n r hr hU (hpos m r hr)
    have heq : J.D k x v = Jcan.D k x v := congrArg
      (fun Q : X [×k]→L[ℝ] ℝ => Q v)
      (HasProjectiveJetsOn.unique hU J.hasProjectiveJetsOn Jcan.hasProjectiveJetsOn k x hx)
    rw [heq]
    have hb := affineOpticalRadialJetSmoothDirections_endpoint_bound
      (L m) (hI m) (hq m) (hg m) n k hkpos r hr hU (hpos m r hr) hx v
      (hδ m r hr).1 (hc m) (hA₀ 0 m) (hlower m r hr x hx) (hupper m r hr x hx)
      (fun j => A j m) (fun j => B j m) (fun j => hA₀ j m) (fun j => hB₀ j m)
      (fun i => p (v i)) (fun i => apply_nonneg _ _) (hH m) (hHR m)
      (fun j _ => hqjet m r hr x hx j) (fun i j _ => hgjet m r hr (v i) j)
    have hmajorant : 0 ≤ endpointRootProductMajorant (c m) (A 0 m)
        (fun j => A j m) (fun j => B j m) k n :=
      endpointRootProductMajorant_nonneg (hc m).le _ _ (fun j => hA₀ j m)
        (fun j => hB₀ j m) k n
    have hsqrt : (|rpowJetCoefficient (1 / 2) k| * Real.sqrt (δ m r) *
        endpointRootProductMajorant (c m) (A 0 m) (fun j => A j m) (fun j => B j m) k n) *
          R ^ (k - 1) ≤ C * E m ^ D := by
      calc
        _ ≤ (|rpowJetCoefficient (1 / 2) k| * Real.sqrt width *
            endpointRootProductMajorant (c m) (A 0 m) (fun j => A j m) (fun j => B j m) k n) *
              R ^ (k - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hδ m r hr).2) (abs_nonneg _))
                hmajorant) (pow_nonneg hR.le _)
        _ = d * endpointRootProductMajorant (c m) (A 0 m)
            (fun j => A j m) (fun j => B j m) k n := by dsimp only [d]; ring
        _ ≤ _ := henvelope m
    apply hb.trans
    simp only [parameterHeightWeight, if_neg hk]
    calc
      _ = ((|rpowJetCoefficient (1 / 2) k| * Real.sqrt (δ m r) *
          endpointRootProductMajorant (c m) (A 0 m) (fun j => A j m) (fun j => B j m) k n) *
            R ^ (k - 1)) * H m * ∏ i, p (v i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsqrt (hH m))
          (Finset.prod_nonneg (fun i _ => apply_nonneg p _))

/-- Restrict a scalar input envelope to a set with a uniformly bounded
low size. All existential arithmetic is over opaque scalar families. -/
private theorem opticalSquare_inputBounds_on_set
    {X Y ι : Type*} (U : Set X) (I : ι → Set ℝ)
    (δ : ι → ℝ → ℝ) (E : ι → ℝ)
    (F : ℕ → ι → ℝ → Y → ℝ) (G : ℕ → ι → ℝ → X → ℝ)
    (project : X → Y) (size : Y → ℝ)
    (hE : ∀ m, 1 ≤ E m)
    (hδ : ∀ m r, r ∈ I m → 0 ≤ δ m r)
    {Q : ℝ} (hQ : 0 < Q)
    (hsize : ∀ x ∈ U, 1 + size (project x) ≤ Q)
    (heq : ∀ j m r, r ∈ I m → ∀ x ∈ U,
      G j m r x = F j m r (project x))
    (hraw : ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ y,
        δ m r ^ j * |F j m r y| ≤
          B * E m ^ A * δ m r * (1 + size y)) :
    ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ x ∈ U,
        δ m r ^ j * |G j m r x| ≤ B * E m ^ A * δ m r := by
  intro j
  obtain ⟨B, A, hB, hA, hb⟩ := hraw j
  refine ⟨B * Q, A, mul_pos hB hQ, hA, fun m r hr x hx => ?_⟩
  rw [heq j m r hr x hx]
  exact (hb m r hr (project x)).trans
    ((mul_le_mul_of_nonneg_left (hsize x hx)
      (mul_nonneg (mul_nonneg hB.le
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hδ m r hr))).trans_eq (by ring))

/-- A scalar direction envelope pulls back along the actual projection
without unpacking its existential at a concrete topological state type. -/
private theorem opticalDirection_inputBounds_pullback
    {X Y ι : Type*} (I : ι → Set ℝ) (δ : ι → ℝ → ℝ) (E H : ι → ℝ)
    (F : ℕ → ι → ℝ → Y → ℝ) (G : ℕ → ι → ℝ → X → ℝ)
    (project : X → Y) (size : Y → ℝ) (p : X → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hδ : ∀ m r, r ∈ I m → 0 ≤ δ m r)
    (hp : ∀ v, size (project v) ≤ p v)
    (heq : ∀ j m r, r ∈ I m → ∀ v,
      |G j m r v| = |F j m r (project v)|)
    (hraw : ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v,
        δ m r ^ j * |F j m r v| ≤
          B * H m * E m ^ A * δ m r * size v) :
    ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v,
        δ m r ^ j * |G j m r v| ≤
          B * E m ^ A * δ m r * H m * p v := by
  intro j
  obtain ⟨B, A, hB, hA, hb⟩ := hraw j
  refine ⟨B, A, hB, hA, fun m r hr v => ?_⟩
  rw [heq j m r hr v]
  have hcoefficient : 0 ≤ B * H m * E m ^ A * δ m r :=
    mul_nonneg (mul_nonneg (mul_nonneg hB.le (hH m))
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hδ m r hr)
  exact (hb m r hr (project v)).trans
    ((mul_le_mul_of_nonneg_left (hp v) hcoefficient).trans_eq (by ring))

/-- Change the scalar family in the complete jet-bound existential.
The genuine directional maps are unchanged by value congruence. -/
private theorem opticalMaterialBounds_family_congr
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (U : Set X) (I : ι → Set ℝ)
    (δ : ι → ℝ → ℝ) (E H : ι → ℝ)
    (F G : ι → ℝ → X → ℝ) (n k : ℕ)
    (heq : ∀ m r, r ∈ I m → ∀ x ∈ U, F m r x = G m r x)
    (hbound : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I m), ∀ J : SmoothDirections U (F m r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * |J.D k x v| ≤
          B * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i)) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I m), ∀ J : SmoothDirections U (G m r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * |J.D k x v| ≤
          B * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i) := by
  obtain ⟨B, A, hB, hA, hb⟩ := hbound
  refine ⟨B, A, hB, hA, fun m r hr J x hx v => ?_⟩
  exact hb m r hr (J.congr (fun y hy => (heq m r hr y hy).symm)) x hx v

/-- The half-reference lower bound selects one radius before any bound
order; the output analytic proposition remains opaque. -/
private theorem opticalMaterialBounds_radius_continuation
    {X ι : Type*} (U : ℕ → ℝ → Set X) (I : ι → Set ℝ)
    (δ : ι → ℝ → ℝ) (E : ι → ℝ)
    (qref : ι → ℝ → ℝ) (q : X → ι → ℝ → ℝ)
    (P : ℝ → Prop) (B : ℝ → ℕ → ℕ → ℕ → Prop)
    (hcommon : ∃ ε : ℝ, 0 < ε ∧ P ε)
    (hhalf : ∀ ε, P ε → ∀ base x, x ∈ U base ε →
      ∀ m r, r ∈ I m → qref m r / 2 ≤ q x m r)
    (href : ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ I m →
      K⁻¹ * E m ^ (-K) * δ m r ≤ qref m r)
    (hcontinue : ∀ ε : ℝ, ∀ base : ℕ, ∀ c₀ K : ℝ,
      0 < ε → 0 < c₀ → 0 < K →
      (∀ x ∈ U base ε, ∀ m r, r ∈ I m →
        c₀ * E m ^ (-K) * δ m r ≤ q x m r) →
      ∀ n k : ℕ, B ε base n k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ base n k : ℕ, B ε base n k := by
  obtain ⟨ε, hε, hp⟩ := hcommon
  obtain ⟨K, hK, hq⟩ := href
  refine ⟨ε, hε, fun base n k => ?_⟩
  exact hcontinue ε base (K⁻¹ / 2) K hε
    (div_pos (inv_pos.mpr hK) (by norm_num)) hK
    (fun x hx m r hr => by
      calc
        _ = (K⁻¹ * E m ^ (-K) * δ m r) / 2 := by ring
        _ ≤ qref m r / 2 := div_le_div_of_nonneg_right (hq m r hr) (by norm_num)
        _ ≤ q x m r := hhalf ε hp base x hx m r hr) n k


/-- The scalar affine-control formula identifies the actual square family
before the complete material bound is specialized to a state model. -/
private theorem opticalMaterialBounds_of_affine_control
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : Seminorm ℝ X) {U : Set X} (hU : IsOpen U)
    (I : ι → Set ℝ) (hI : ∀ m, IsOpen (I m))
    (q₀ g : ι → ℝ → ℝ) (L : ι → X →L[ℝ] ℝ)
    (κ : ι → X → ℝ) (hL : ∀ m x, L m x = κ m x)
    (F : ι → X → ℝ → ℝ)
    (hvalue : ∀ m r, r ∈ I m → ∀ x ∈ U,
      F m x r = q₀ m r - κ m x * g m r)
    (hq : ∀ m, ContDiffOn ℝ ∞ (q₀ m) (I m))
    (hg : ∀ m, ContDiffOn ℝ ∞ (g m) (I m))
    (δ : ι → ℝ → ℝ) (E H : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    {width c₀ K : ℝ} (hwidth : 0 < width)
    (hheight : ∃ R : ℝ, 0 < R ∧ ∀ m, H m ≤ R)
    (hc₀ : 0 < c₀) (hK : 0 < K)
    (hδ : ∀ m r, r ∈ I m → 0 < δ m r ∧ δ m r ≤ width)
    (hlower : ∀ x ∈ U, ∀ m r, r ∈ I m →
      c₀ * E m ^ (-K) * δ m r ≤ F m x r)
    (hjetF : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ x ∈ U,
        δ m r ^ j * |iteratedDeriv j (F m x) r| ≤
          C * E m ^ A * δ m r)
    (hjetg : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v : X,
        δ m r ^ j * |κ m v * iteratedDeriv j (g m) r| ≤
          C * E m ^ A * δ m r * H m * p v)
    (n k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I m),
      ∀ J : SmoothDirections U
        (fun x => iteratedDeriv n (fun s => Real.sqrt (F m x s)) r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * |J.D k x v| ≤
          C * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i) := by
  obtain ⟨R, hR, hHR⟩ := hheight
  have heq (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) :
      q₀ m r + L m x * (-g m r) = F m x r := by
    rw [hvalue m r hr x hx, hL m x]
    ring
  have hlow (m r) (hr : r ∈ I m) (x) (hx : x ∈ U) :
      c₀ * E m ^ (-K) * δ m r ≤ q₀ m r + L m x * (-g m r) := by
    rw [heq m r hr x hx]
    exact hlower x hx m r hr
  have hqraw : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ x ∈ U,
        δ m r ^ j * |iteratedDeriv j
          (fun s => q₀ m s + L m x * (-g m s)) r| ≤
            C * E m ^ A * δ m r := by
    intro j
    obtain ⟨C, A, hC, hA, hb⟩ := hjetF j
    refine ⟨C, A, hC, hA, fun m r hr x hx => ?_⟩
    have he : (fun s => q₀ m s + L m x * (-g m s)) =ᶠ[𝓝 r] F m x := by
      filter_upwards [(hI m).mem_nhds hr] with s hs
      exact heq m s hs x hx
    rw [he.iteratedDeriv_eq j]
    exact hb m r hr x hx
  have hgraw : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m → ∀ v : X,
        δ m r ^ j * |iteratedDeriv j (fun s => L m v * (-g m s)) r| ≤
          C * E m ^ A * δ m r * H m * p v := by
    intro j
    obtain ⟨C, A, hC, hA, hb⟩ := hjetg j
    refine ⟨C, A, hC, hA, fun m r hr v => ?_⟩
    have he : iteratedDeriv j (fun s => L m v * (-g m s)) r =
        -(κ m v * iteratedDeriv j (g m) r) := by
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_neg, hL m v, mul_neg]
    rw [he, abs_neg]
    exact hb m r hr v
  exact opticalMaterialBounds_family_congr p U I δ E H
    (fun m r x => iteratedDeriv n
      (fun s => Real.sqrt (q₀ m s + L m x * (-g m s))) r)
    (fun m r x => iteratedDeriv n (fun s => Real.sqrt (F m x s)) r) n k
    (fun m r hr x hx => by
      apply Filter.EventuallyEq.iteratedDeriv_eq
      filter_upwards [(hI m).mem_nhds hr] with s hs
      exact congrArg Real.sqrt (heq m s hs x hx))
    (affineOpticalRadialJet_material_bounds p hU I hI q₀ (fun m r => -g m r)
      L hq (fun m => (hg m).neg) δ E H hE hH hwidth hR hHR hc₀ hK
      hδ hlow hqraw hgraw n k)

/-- The endpoint distance is positive inside the component and bounded
by the fixed total width. -/
private theorem opticalMaterial_componentDistance
    {a b l h r : ℝ} (hal : a < l) (hhb : h < b) (hr : r ∈ Ioo l h) :
    0 < min (r - l) (h - r) ∧ min (r - l) (h - r) ≤ b - a := by
  refine ⟨lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2), ?_⟩
  linarith [hr.2, min_le_left (r - l) (h - r)]

/-- Eliminate the scalar material bound without exposing any concrete
state-valued analytic conclusion. -/
private theorem opticalMaterial_componentHeight
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (cell : ℕ → ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ R := by
  obtain ⟨R, hR, hb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  exact ⟨R, hR, fun m => by
    simpa only [Real.rpow_zero, mul_one] using
      hb _ (materialSample_mem_radialCore hT hRef.choose_spec.2.1 (cell m))⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev opticalMaterialStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] opticalMaterialStateTopology
private abbrev opticalMaterialStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] opticalMaterialStateGroup
private abbrev opticalMaterialStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] opticalMaterialStateModule
private abbrev opticalMaterialStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (opticalMaterialStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] opticalMaterialStateSMul


/-- The actual optical square on the common ball, before any affine
continuous-linear representation or square-root operation is introduced. -/
private theorem n01_opticalSquare_neighborhood_input
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    {base : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      ∀ z ∈ stateNeighborhood S C base ε,
        min (r - C.left m) (C.right m - r) ^ j *
          |iteratedDeriv j (fun s => -deriv (stateProfile D S C z.1) s /
            (s * stateProfile D S C z.1 s)) r| ≤
          B * T.E0 (T.sample (C.cell m)) ^ A *
            min (r - C.left m) (C.right m - r) :=
  opticalSquare_inputBounds_on_set
    (stateNeighborhood S C base ε) (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun j _ r (x : AnnularState S) => iteratedDeriv j
      (fun s => -deriv (stateProfile D S C x) s / (s * stateProfile D S C x s)) r)
    (fun j _ r (z : AnnularState S × ℝ) => iteratedDeriv j
      (fun s => -deriv (stateProfile D S C z.1) s / (s * stateProfile D S C z.1 s)) r)
    (fun z : AnnularState S × ℝ => z.1) (stateGrading S 0)
    (fun m => hE _
      (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
    (fun _ _ hr => (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le)
    (Q := 1 + stateGrading S 0 C.referenceState + ε)
    (by linarith [apply_nonneg (stateGrading S 0) C.referenceState])
    (fun z hz => by linarith [stateGrading_zero_le_reference_add_radius hz])
    (fun _ _ _ _ _ _ => rfl)
    (fun j => stateOpticalSquare_weighted_sample_bound hS hT hA hE hloc j)

/-- Pull the genuine optical direction back to joint states. The scalar
direction formula stays separate from the continuous-linear map. -/
private theorem n01_opticalDirection_joint_input
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∀ j : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ v : AnnularState S × ℝ,
        min (r - C.left m) (C.right m - r) ^ j *
          |stateKappa S v.1 m * iteratedDeriv j (controlOpticalFactor C m) r| ≤
          B * T.E0 (T.sample (C.cell m)) ^ A *
            min (r - C.left m) (C.right m - r) *
              (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) *
                pairGrading (stateGrading S) realGrading 0 v :=
  opticalDirection_inputBounds_pullback
    (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun j m r (v : AnnularState S) =>
      stateKappa S v m * iteratedDeriv j (controlOpticalFactor C m) r)
    (fun j m r (v : AnnularState S × ℝ) =>
      stateKappa S v.1 m * iteratedDeriv j (controlOpticalFactor C m) r)
    (fun v : AnnularState S × ℝ => v.1) (stateGrading S 0)
    (pairGrading (stateGrading S) realGrading 0)
    (fun m => hE _
      (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
    (fun m => Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m))).2.1.le _)
    (fun _ _ hr => (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le)
    (stateGrading_fst_le_jointStateGrading S 0)
    (fun _ _ _ _ _ => rfl)
    (fun j => stateOpticalDirection_weighted_sample_bound hS hT hA hE j)

/-- An explicit pointwise lower bound for the actual optical square gives
all radial/parameter orders, using only level-zero direction seminorms. -/
theorem n01_stateOpticalRadialJet_material_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    {base : ℕ} {ε c₀ K : ℝ} (hε : 0 < ε) (hc₀ : 0 < c₀) (hK : 0 < K)
    (hlower : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        c₀ * T.E0 (T.sample (C.cell m)) ^ (-K) *
            min (r - C.left m) (C.right m - r) ≤
          -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r))
    (n k : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv n (fun s => Real.sqrt
          (-deriv (stateProfile D S C z.1) s / (s * stateProfile D S C z.1 s))) r),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → AnnularState S × ℝ,
        min (r - C.left m) (C.right m - r) ^ n * |J.D k z v| ≤
          B * T.E0 (T.sample (C.cell m)) ^ A *
            parameterHeightWeight (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) k *
              ∏ i, pairGrading (stateGrading S) realGrading 0 (v i) := by
  exact opticalMaterialBounds_of_affine_control
    (pairGrading (stateGrading S) realGrading 0)
    (isOpen_stateNeighborhood S C base ε)
    (fun m => Ioo (C.left m) (C.right m)) (fun _ => isOpen_Ioo)
    (fun _ => referenceOpticalSquare D) (controlOpticalFactor C)
    (stateJointKappaCLM hS hT hA.1.1)
    (fun m z => stateKappa S z.1 m)
    (stateJointKappaCLM_apply hS hT hA.1.1)
    (fun _ z r => -deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r))
    (fun m r hr z _ => by
      simpa only [iteratedDeriv_zero] using
        n01_stateProfile_opticalSquare_iteratedDeriv_eq hA z.1 m 0 hr)
    (fun m r hr =>
      (referenceOpticalSquare_contDiffAt hA.1.1.choose_spec.1
        ⟨(hA.2.2.1.1 m).1.trans hr.1,
          hr.2.trans (hA.2.2.1.1 m).2.2⟩).contDiffWithinAt)
    (fun m r hr =>
      (controlOpticalFactor_contDiffAt hA.1.1.choose_spec.1 hA.2.2.1 m hr).contDiffWithinAt)
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m => hE _
      (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
    (fun m => Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m))).2.1.le _)
    (sub_pos.mpr hA.1.1.choose_spec.1.2.1)
    (opticalMaterial_componentHeight hT hA.1.1 C.cell) hc₀ hK
    (fun m _ hr => opticalMaterial_componentDistance
      (hA.2.2.1.1 m).1 (hA.2.2.1.1 m).2.2 hr)
    hlower
    (n01_opticalSquare_neighborhood_input hS hT hA hE hloc hε)
    (n01_opticalDirection_joint_input hS hT hA hE) n k

/-- A single optical neighbourhood suffices at every spatial and
parameter order, starting only from the quantitative reference lower
bound and the original physical control estimates. -/
theorem n01_exists_stateOpticalRadialJet_material_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
            min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ base n k : ℕ,
      ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv n (fun s => Real.sqrt
          (-deriv (stateProfile D S C z.1) s / (s * stateProfile D S C z.1 s))) r),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → AnnularState S × ℝ,
        min (r - C.left m) (C.right m - r) ^ n * |J.D k z v| ≤
          B * T.E0 (T.sample (C.cell m)) ^ A *
            parameterHeightWeight (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)) k *
              ∏ i, pairGrading (stateGrading S) realGrading 0 (v i) := by
  exact opticalMaterialBounds_radius_continuation
    (stateNeighborhood S C) (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun _ r => -deriv D.w r / (r * D.w r))
    (fun z _ r => -deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r)) _ _
    (n01_exists_common_opticalBounds_of_referenceLower hS hT hA hlower)
    (fun ε hb base z hz m r hr => (hb base z hz m r hr).2.1)
    hlower
    (fun ε base c₀ K hε hc₀ hK hlow n k =>
      n01_stateOpticalRadialJet_material_bounds hS hT hA hE hloc
        hε hc₀ hK hlow n k)

end ContinuousFlexibility.Statements
