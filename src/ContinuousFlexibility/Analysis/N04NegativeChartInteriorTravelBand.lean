import ContinuousFlexibility.Analysis.N04NegativeChartInteriorTravelPrefix
import ContinuousFlexibility.Analysis.N04NegativeChartCurrentPositiveBand
import ContinuousFlexibility.Analysis.N04NegativeChartPositivePowerBounds

/-! A single state neighborhood gives the actual interior travel a material
value interval, while retaining every finite mixed prefix on that neighborhood. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped BigOperators

/-- The fractional estimate is normalized without changing either seminorm. -/
theorem n04NegativeChart_fractional_oneHigh
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {k : ℕ} (A : X [×k]→L[ℝ] ℝ) (p : ℕ → Seminorm ℝ X)
    (base high : ℕ) (x : X) {M β : ℝ} (hM : 0 ≤ M) (hβ : β ≤ 1)
    (hraw : ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ i, p high (v i) ≤ R) →
        |A v| ≤ M * R ^ β) :
    ∀ v : Fin k → X, |A v| ≤ M * oneHighVariationWeight p base high x v := by
  have hn := multilinear_bound_of_unitBall A (normSeminorm ℝ ℝ)
    (p base) (p high) (a := 1 + p high x) hM
    (fun v hv => by
      let R : ℝ := 1 + p high x + ∑ i, p high (v i)
      have hs : 0 ≤ ∑ i, p high (v i) := Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hx : 0 ≤ p high x := apply_nonneg _ _
      have hR : 1 ≤ R := by dsimp only [R]; linarith only [hs, hx]
      have hxR : p high x ≤ R := by dsimp only [R]; linarith only [hs]
      have hvR (i : Fin k) : p high (v i) ≤ R :=
        (Finset.single_le_sum (f := fun j => p high (v j))
          (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity : 0 ≤ 1 + p high x))
      have hb := (hraw v (fun i => (hv i).le) R hR hxR hvR).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hR hβ) hM)
      simpa only [coe_normSeminorm, Real.norm_eq_abs, R] using hb)
  simpa only [coe_normSeminorm, Real.norm_eq_abs, multilinearTameSize,
    oneHighVariationWeight] using hn

private theorem interior_scaled_reference_inverse {t M : ℝ}
    (ht : 0 < t) (hM : t⁻¹ ≤ M) :
    0 < (3 / 2 : ℝ) * t ∧ ((3 / 2 : ℝ) * t)⁻¹ ≤ M := by
  exact ⟨mul_pos (by norm_num) ht,
    (inv_anti₀ ht (le_mul_of_one_le_left ht.le (by norm_num))).trans hM⟩

private theorem interior_material_lower {f B E A : ℝ}
    (hf : 0 < f) (hE : 0 < E) (hi : f⁻¹ ≤ 2 * B * E ^ A) :
    (2 * B)⁻¹ * E ^ (-A) ≤ f := by
  have h := inv_le_of_inv_le₀ hf hi
  simpa only [mul_inv_rev, Real.rpow_neg hE.le, mul_comm] using h

namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true

variable (W : N04RealizationStart)

/-- The same actual mixed prefix, exposed for restriction of the state sector. -/
def NegativeInteriorScaledTravelPrefix
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ) (base : ℕ) (ε : ℝ) : Prop :=
  ∀ K : ℕ, ∃ D : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ k a b : ℕ, k ≤ K → a + b ≤ s → ∀ m side q,
    q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b (W.negativeScaledOrientedTravel m side z) q),
    ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin k → Parameter W.S,
    (∀ i, parameterGrading W.S base (v i) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
    parameterGrading W.S (s + D * K + base + 1) z ≤ R →
    (∀ i, parameterGrading W.S (s + D * K + base + 1) (v i) ≤ R) →
    |J.D k z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
      parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
        R ^ (((a + b + D * k : ℕ) : ℝ) / ((s + D * K : ℕ) + 1 : ℝ))

theorem NegativeInteriorScaledTravelPrefix.mono
    {e : ℕ ≃ N04PieceIndex W.D} {ρ : ℕ → Bool → ℝ}
    (hρ : ∀ m side, 0 < ρ m side) {base base' : ℕ} {ε ε' : ℝ}
    (h : W.NegativeInteriorScaledTravelPrefix e ρ base ε)
    (hbW : W.base ≤ base) (hεW : ε ≤ W.ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    W.NegativeInteriorScaledTravelPrefix e ρ base' ε' := by
  intro K
  have hd := h K
  refine ⟨hd.choose, fun s => ?_⟩
  have hs := hd.choose_spec s
  refine ⟨hs.choose, hs.choose_spec.1, fun k a b hk hab m side q hq J z hz v hv R hR hzR hvR => ?_⟩
  have hqΩ := W.negativeInteriorPhysicalDomain_subset ρ hρ (m, side) hq
  let J₀ := (W.negativeScaledOrientedTravelMixedRegularity m side hbW hεW).parameter a b q hqΩ
  have hsub := sectorNeighborhood_mono W.S hb hε hε
  have he : J.D k z v = J₀.D k z v := congrArg
    (fun A : Parameter W.S [×k]→L[ℝ] ℝ => A v)
    (J.unique (J₀.restrict (sectorNeighborhood_isOpen W.S base' ε' ε') hsub) k z hz)
  have hh : s + hd.choose * K + base + 1 ≤ s + hd.choose * K + base' + 1 := by omega
  have hp := n07aParameterGrading_monotone W.S
  exact (congrArg abs he).trans_le (hs.choose_spec.2 k a b hk hab m side q hq J₀ z (hsub hz) v
    (fun i => (hp hb (v i)).trans (hv i)) R hR ((hp hh z).trans hzR)
    (fun i => (hp hh (v i)).trans (hvR i)))

/-- The interval and the state sector are chosen before all jet orders. -/
structure NegativeInteriorTravelControl
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ) where
  base : ℕ
  ε : ℝ
  base_le : W.base ≤ base
  ε_pos : 0 < ε
  ε_le : ε ≤ min W.ε (1 / 2 : ℝ)
  lower : ℝ
  upper : ℝ
  lowerPower : ℝ
  upperPower : ℝ
  lower_pos : 0 < lower
  upper_nonneg : 0 ≤ upper
  lowerPower_nonneg : 0 ≤ lowerPower
  upperPower_nonneg : 0 ≤ upperPower
  «prefix» : W.NegativeInteriorScaledTravelPrefix e ρ base ε
  values : ∀ m side q, q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) →
    ∀ z ∈ sectorNeighborhood W.S base ε ε,
      lower * W.T.E0 (W.negativeHalfSample e m side) ^ (-lowerPower) ≤
        W.negativeScaledOrientedTravel m side z q ∧
      W.negativeScaledOrientedTravel m side z q ≤
        upper * W.T.E0 (W.negativeHalfSample e m side) ^ upperPower

theorem negativeScaledOrientedTravel_le_total (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint} (hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    W.negativeScaledOrientedTravel m side z q ≤ (3 / 2 : ℝ) * W.C.travel m := by
  have ht := (n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field
    (liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m).mapsTo hq
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h := ht.1
  cases side
  · exact h.2.le
  · change W.C.travel m - _ ≤ W.C.travel m
    exact sub_le_self _ h.1.le

/-- The single first-jet shrink ranges over every component, side and
interior point. No later parameter or spatial order changes it. -/
theorem negativeInteriorTravelControl_nonempty
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    Nonempty (W.NegativeInteriorTravelControl e ρ) := by
  have hex := W.negativeInterior_scaledTravel_prefix e ρ hρ hρb
  let b₀ := hex.choose
  let ε₀ := hex.choose_spec.choose
  have hs := hex.choose_spec.choose_spec
  have hp : W.NegativeInteriorScaledTravelPrefix e ρ b₀ ε₀ := hs.2.2.2
  have hd := hp 1
  let D := hd.choose
  have hc := hd.choose_spec 0
  let C := hc.choose
  let F : W.NegativeOpticalFactors e := Classical.choice (W.negativeOpticalFactors_nonempty e)
  have href := F.interior_referenceTravel_inverse_material ρ hρ hρb
  let B := href.choose
  let A := href.choose_spec.choose
  have hr := href.choose_spec.choose_spec
  let I := Σ i : ℕ × Bool, W.negativeInteriorPhysicalDomain ρ i
  let sample : I → ℕ := fun i => (W.A e).cell (e.symm (.inl i.1))
  let f : I → Parameter W.S → ℝ := fun i z =>
    W.negativeScaledOrientedTravel i.1.1 i.1.2 z i.2.val
  have hq (i : I) := W.negativeInteriorPhysicalDomain_subset ρ
    (fun m side => (hρ m side).1) i.1 i.2.property
  let J (i : I) : SmoothDirections (sectorNeighborhood W.S b₀ ε₀ ε₀) (f i) :=
    ((W.negativeScaledOrientedTravelMixedRegularity i.1.1 i.1.2 hs.1
      (hs.2.2.1.trans (min_le_left _ _))).parameter 0 0 i.2.val (hq i)).congr
      (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero, f])
  have hreference (i : I) : 0 < f i 0 ∧
      (f i 0)⁻¹ ≤ B * W.T.E0 (W.T.sample (sample i)) ^ A := by
    rcases i.2.property with ⟨p, hpq, heq⟩
    have hb := hr.2.2 i.1.1 i.1.2 p.1 hpq.1
    change 0 < W.negativeScaledOrientedTravel i.1.1 i.1.2 0 i.2.val ∧
      (W.negativeScaledOrientedTravel i.1.1 i.1.2 0 i.2.val)⁻¹ ≤
        B * W.T.E0 (W.negativeHalfSample e i.1.1 i.1.2) ^ A
    rw [W.negativeScaledOrientedTravel_reference i.1.1 i.1.2 (hq i)]
    simpa only [← heq, negativeInwardPoint] using interior_scaled_reference_inverse hb.1 hb.2
  have hfirst (i : I) (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S b₀ ε₀ ε₀)
      (v : Fin 1 → Parameter W.S) :
      |(J i).D 1 z v| ≤ C * W.T.E0 (W.T.sample (sample i)) ^ C *
        W.T.H (W.T.sample (sample i)) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading W.S) b₀ (D + b₀ + 1) z v := by
    let E := W.T.E0 (W.T.sample (sample i))
    let H := W.T.H (W.T.sample (sample i)) ^ (3 / 4 : ℝ)
    have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
    have hβ : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    apply n04NegativeChart_fractional_oneHigh ((J i).D 1 z) (parameterGrading W.S)
      b₀ (D + b₀ + 1) z
      (mul_nonneg (mul_nonneg hc.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (W.floor _)) _)) hH)
      hβ _ v
    intro w hw R hR hzR hwR
    let K : SmoothDirections (sectorNeighborhood W.S b₀ ε₀ ε₀)
        (fun x => mixedDerivative 0 0
          (W.negativeScaledOrientedTravel i.1.1 i.1.2 x) i.2.val) :=
      (J i).congr (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero, f])
    have hh := hc.choose_spec.2 1 0 0 le_rfl (by omega) i.1.1 i.1.2 i.2.val
      i.2.property K z hz w hw R hR
      (by simpa only [Nat.zero_add, Nat.mul_one] using hzR)
      (fun j => by simpa only [Nat.zero_add, Nat.mul_one] using hwR j)
    simpa only [K, SmoothDirections.congr, Nat.zero_add, Nat.mul_one, Nat.cast_add,
      Nat.cast_one, parameterHeightWeight, Nat.one_ne_zero, if_false] using hh
  have hband := n04NegativeChart_current_half_reference W.radial.1 W.hT sample
    b₀ (D + b₀ + 1) ε₀ hs.2.1 f J C C B A hc.choose_spec.1 hr.1 hreference hfirst
  let base := hband.choose
  let ε := hband.choose_spec.choose
  have hb := hband.choose_spec.choose_spec
  have hu := W.negativeTravel_material_upper e
  let Cu := hu.choose
  let Au := hu.choose_spec.choose
  have hu' := hu.choose_spec.choose_spec
  refine ⟨{ base := base, ε := ε, base_le := hs.1.trans hb.1, ε_pos := hb.2.1,
    ε_le := le_min (hb.2.2.1.trans (hs.2.2.1.trans (min_le_left _ _))) hb.2.2.2.1,
    lower := (2 * B)⁻¹, upper := (3 / 2 : ℝ) * Cu, lowerPower := A, upperPower := Au,
    lower_pos := inv_pos.mpr (mul_pos (by norm_num) hr.1),
    upper_nonneg := mul_nonneg (by norm_num) hu'.1.le,
    lowerPower_nonneg := hr.2.1, upperPower_nonneg := hu'.2.1,
    «prefix» := NegativeInteriorScaledTravelPrefix.mono W (fun m side => (hρ m side).1) hp hs.1
      (hs.2.2.1.trans (min_le_left _ _)) hb.1 hb.2.2.1,
    values := fun m side q hqi z hz => ?_ }⟩
  let i : I := ⟨(m, side), ⟨q, hqi⟩⟩
  have hval := hb.2.2.2.2 i z hz
  refine ⟨interior_material_lower hval.2.1 (zero_lt_one.trans_le (W.floor _)) hval.2.2, ?_⟩
  have hz₀ := sectorNeighborhood_mono W.S (hs.1.trans hb.1)
    (hb.2.2.1.trans (hs.2.2.1.trans (min_le_left _ _)))
    (hb.2.2.1.trans (hs.2.2.1.trans (min_le_left _ _))) hz
  have ht := (W.negativeScaledOrientedTravel_le_total m side hz₀ (hq i)).trans
    (mul_le_mul_of_nonneg_left (hu'.2.2 m side) (by norm_num : (0 : ℝ) ≤ 3 / 2))
  exact ht.trans_eq (mul_assoc _ _ _).symm

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInteriorTravelControl_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInteriorTravelControl_nonempty
