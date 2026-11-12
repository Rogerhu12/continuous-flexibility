import ContinuousFlexibility.Analysis.N01cPhysicalLiePrefixBounds
import ContinuousFlexibility.Analysis.N01cPhysicalFlowPointBounds
import ContinuousFlexibility.Analysis.N01cPhysicalFlowAngularInputs

/-!
# Fixed-order positive physical radial flow bounds

The outer Lie jets come from the whole speed's actual endpoint estimate.
The inner angular jets come from the proved zero-parameter growth and
positive-parameter angular estimates. One common interpolation base
controls the complete graph term, with all parameter losses counted in
its total spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]

theorem physicalFlow_positiveMixed_fixed_bound
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (center : X)
    (base lossRaw lossIz lossIp o₀ : ℕ)
    (U : Set X) (I : ι → Set ℝ) (hU : IsOpen U) (hI : ∀ m, IsOpen (I m))
    (δ : ι → ℝ → ℝ) (H E : ι → ℝ) (lam Θ : ι → X → PolarPoint → ℝ)
    (F : ∀ m, MixedJetRegularity U (I m ×ˢ (univ : Set ℝ)) (lam m))
    (hf : EndpointMixedPowerBounds p center base lossRaw U
      (fun m => I m ×ˢ (univ : Set ℝ)) (fun m q => δ m q.1)
      (fun m _ => H m) (fun m _ => E m) lam)
    (hΘ : ∀ m x, x ∈ U → ContDiffOn ℝ ∞ (Θ m x) (I m ×ˢ (univ : Set ℝ)))
    (hODE : ∀ m x, x ∈ U → ∀ r ∈ I m, ∀ θ : ℝ,
      HasDerivAt (fun t => Θ m x (t, θ)) (lam m x (r, Θ m x (r, θ))) r)
    (Jlam : ∀ m a r, r ∈ I m → SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun q => mixedDerivative a 0 (lam m q.1) (r, q.2)))
    (JΘ : ∀ m r, r ∈ I m → SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun q => Θ m q.1 (r, q.2)))
    (hδ : ∀ m r, r ∈ I m → 0 ≤ δ m r)
    {width RH : ℝ} (hwidth : ∀ m r, r ∈ I m → δ m r ≤ width)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m ∧ H m ≤ RH)
    (hunit : ∀ x ∈ U, p base (x - center) ≤ 1)
    (hIz : SpatialPowerInterpolation p base lossIz o₀)
    (hIp : SpatialPowerInterpolation p base lossIp 0)
    (K offset n b k S : ℕ) (hk : 0 < k) (hkK : k ≤ K)
    (hNS : (b + k) + offset ≤ S)
    (horder : n + b + (offset + 1) * k ≤ S)
    (hzero : ∀ β : ℕ, 1 ≤ β → ∃ C : ℝ, 0 < C ∧
      ∀ m r, r ∈ I m → ∀ θ x, x ∈ U →
        |iteratedDeriv β (fun η => Θ m x (r, η)) θ| ≤
          C * (1 + p (β - 1 + o₀) (x - center)))
    (hpositive : ∀ β : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m r, r ∈ I m → ∀ θ : ℝ,
      ∀ J : SmoothDirections U
        (fun x => iteratedDeriv β (fun η => Θ m x (r, η)) θ),
      ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
        |J.D j x v| ≤ C * H m * E m ^ A *
          oneHighVariationWeight p base (β + offset) (x - center) v) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m r, r ∈ I m → ∀ θ : ℝ,
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative (n + 1) b (Θ m x) (r, θ)),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ (n + 1) * |J.D k x v| ≤ C * H m * E m ^ A *
          oneHighVariationWeight p base
            (S + max lossRaw (max lossIz lossIp)) (x - center) v := by
  classical
  let N : ℕ := b + k
  have hnk : k ≤ (offset + 1) * k := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right k (Nat.succ_le_succ (Nat.zero_le offset))
  have hnN : n + N ≤ S := by dsimp only [N]; omega
  obtain ⟨C₀, A₀, hC₀, hA₀, ho⟩ :=
    endpointMixedPowerBounds_physicalLiePrefix hU
      (fun m => (hI m).prod isOpen_univ) F hf
      (fun m q hq => hδ m q.1 hq.1)
      (fun m q hq => hwidth m q.1 hq.1)
      (fun m _ _ => hE m) (fun m _ _ => hH m) n N S hnN
  obtain ⟨Cz, Cp, Ap, hCz, hCp, hAp, hz, hpos⟩ :=
    exists_finite_angularFlowJet_constants p center base o₀ K offset N
      U I Θ H E (fun m => (hH m).1) hE hzero hpositive
  obtain ⟨Iz, hIz₁, hiz⟩ := hIz S
  obtain ⟨Ip, hIp₁, hip⟩ := hIp S
  let C₁ : ℝ := 1 + 2 * Cz * Iz + Cp * ((K : ℝ) + 2) * Ip
  let L : ℝ := max 1 RH
  let B : ℝ := n01c_graphPartitionWordCount N * (C₀ * C₁ ^ N * L ^ N)
  let A : ℝ := A₀ + Ap * (N : ℝ)
  let high : ℕ := S + max lossRaw (max lossIz lossIp)
  have hCz₀ : 0 ≤ Cz := zero_le_one.trans hCz
  have hCp₀ : 0 ≤ Cp := zero_le_one.trans hCp
  have hIz₀ : 0 ≤ Iz := zero_le_one.trans hIz₁
  have hIp₀ : 0 ≤ Ip := zero_le_one.trans hIp₁
  have hC₁ : 1 ≤ C₁ := by
    have hz₀ : 0 ≤ 2 * Cz * Iz := by positivity
    have hp₀ : 0 ≤ Cp * ((K : ℝ) + 2) * Ip := by positivity
    dsimp only [C₁]
    linarith
  have hL : 1 ≤ L := le_max_left _ _
  have hB : 0 ≤ B := by
    have hc : 0 ≤ n01c_graphPartitionWordCount N :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact mul_nonneg hc
      (mul_nonneg (mul_nonneg (zero_le_one.trans hC₀)
        (pow_nonneg (zero_le_one.trans hC₁) _))
        (pow_nonneg (zero_le_one.trans hL) _))
  have hA : 0 ≤ A := add_nonneg hA₀ (mul_nonneg hAp (Nat.cast_nonneg _))
  have hrawIndex : S + lossRaw ≤ high :=
    Nat.add_le_add le_rfl (le_max_left _ _)
  have hzIndex : S + lossIz ≤ high :=
    Nat.add_le_add le_rfl ((le_max_left _ _).trans (le_max_right _ _))
  have hpIndex : S + lossIp ≤ high :=
    Nat.add_le_add le_rfl ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨1 + B, A, by linarith, hA, ?_⟩
  intro m r hr θ J x hx v
  let JA : ∀ l : ℕ, SmoothDirections U
      (fun y => iteratedDeriv l (fun η => Θ m y (r, η)) θ) :=
    fun l => smoothDirections_angularStateSlice (JΘ m r hr) l θ
  have houter :
      ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      ∀ j l, j + l ≤ b + k → ∀ η,
      ∀ JO : SmoothDirections U
        (fun y => mixedDerivative 0 l (physicalFlowLieJet (lam m y) n) (r, η)),
      ∀ u : Fin j → X, (∀ i, p base (u i) ≤ 1) →
        (∀ i, p high (u i) ≤ R) →
        δ m r ^ (n + 1) * |JO.D j x u| ≤
          C₀ * E m ^ A₀ * parameterHeightWeight (H m) j *
            R ^ (((n + l : ℕ) : ℝ) / ((S : ℝ) + 1)) := by
    intro R hR hxR j l hjl η JO u hu huR
    have hh := ho j l hjl m (r, η) ⟨hr, mem_univ _⟩ JO x hx (hunit x hx)
      u hu R hR ((hp hrawIndex _).trans hxR)
      (fun i => (hp hrawIndex _).trans (huR i))
    simpa only [Real.norm_eq_abs] using hh
  have hflow :
      ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      ∀ j l, 0 < j + l → j + l ≤ b + k → j ≤ k →
      ∀ JL : SmoothDirections U
        (fun y => iteratedDeriv l (fun η => Θ m y (r, η)) θ),
      ∀ u : Fin j → X, (∀ i, p base (u i) ≤ 1) →
        (∀ i, p high (u i) ≤ R) →
        |JL.D j x u| ≤ C₁ * E m ^ Ap * parameterHeightWeight (H m) j *
          R ^ (((if j = 0 then l - 1 else l + offset : ℕ) : ℝ) /
            ((S : ℝ) + 1)) := by
    intro R hR hxR
    have hh := angularFlowJets_spatialPower_bound JA p center base high K N S o₀ offset
      hNS hx (hunit x hx) hR hxR hCz₀ hCp₀ hIz₁ hIp₁ (hE m) hAp (hH m).1
      (fun l hl hlN => hz l hl hlN m r hr θ x hx)
      (fun j hj hjK l hlN u => hpos l hlN m r hr θ (JA l) j hjK hj x hx u)
      (fun a ha y hy hyR => hiz a ha y hy R hR ((hp hzIndex y).trans hyR))
      (fun a ha y hy hyR => by
        simpa only [Nat.add_zero] using
          hip a ha y hy R hR ((hp hpIndex y).trans hyR))
    intro j l hjl hjlN hj JL u hu huR
    have heq : JL.D j x u = (JA l).D j x u :=
      congrArg (fun A : X [×j]→L[ℝ] ℝ => A u)
        (HasProjectiveJetsOn.unique hU JL.hasProjectiveJetsOn
          (JA l).hasProjectiveJetsOn j x hx)
    rw [heq]
    exact hh j (hj.trans hkK) l hjl (by dsimp only [N]; omega) u hu huR
  have hpoint := physicalFlowPositiveMixed_point_oneHigh_bound hU (hI m)
    (F m).spatial (hΘ m) (hODE m) hr
    (fun a => Jlam m a r hr) (JΘ m r hr)
    p center base high n b k S offset hk horder hx θ
    (hδ m r hr) (zero_le_one.trans hC₀) hC₁ (hE m) hAp
    (hH m).1 ((hH m).2.trans (le_max_right 1 RH)) hL houter hflow J v
  have hweight : 0 ≤ H m * E m ^ A *
      oneHighVariationWeight p base high (x - center) v :=
    mul_nonneg (mul_nonneg (hH m).1
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
      (oneHighVariationWeight_nonneg p base high (x - center) v)
  calc
    _ ≤ B * E m ^ A * H m *
        oneHighVariationWeight p base high (x - center) v := hpoint
    _ = B * (H m * E m ^ A *
        oneHighVariationWeight p base high (x - center) v) := by ring
    _ ≤ (1 + B) * (H m * E m ^ A *
        oneHighVariationWeight p base high (x - center) v) :=
      mul_le_mul_of_nonneg_right (by linarith : B ≤ 1 + B) hweight
    _ = _ := by ring

end ContinuousFlexibility.Analysis
