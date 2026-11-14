import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredForwardJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerPrefix

/-!
# Sampled prefixes of the original full forward chart jets

The odd power, even formulas, and label slope can choose different
parameter shifts. Their angular horizons are enlarged before applying
their bounds, making the high denominator exactly common. The fixed
physical unscale preserves the resulting reserve-one word estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_prefix_horizon
    (s K c C : ℕ) (hc : c ≤ C) : s + (C - c) * K + c * K = s + C * K := by
  rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hc]

theorem n04PositiveGeometry_prefix_power_align
    (s K u k c C : ℕ) (hc : c ≤ C) {R : ℝ} (hR : 1 ≤ R) :
    R ^ (((u + c * k : ℕ) : ℝ) /
        (((s + (C - c) * K + c * K : ℕ) : ℝ) + 1)) ≤
      (R ^ (1 / (((s + C * K : ℕ) : ℝ) + 1))) ^ (u + C * k) := by
  rw [n04PositiveGeometry_prefix_horizon s K c C hc,
    ← Real.rpow_mul_natCast (zero_le_one.trans hR)]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hnum : (u + c * k : ℕ) ≤ u + C * k :=
    Nat.add_le_add_left (Nat.mul_le_mul_right k hc) u
  calc
    _ ≤ ((u + C * k : ℕ) : ℝ) / (((s + C * K : ℕ) : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
    _ = _ := by ring

theorem n04PositiveGeometry_storedForwardJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedForwardJet W.S W.C (W.A X.e₀) m (!side) n),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let oddData := n04PositiveGeometry_rootOddPowerTrace_sample_prefix_five
    W X hb hε hεW hεone hflow
  let evenData := n04PositiveGeometry_rootBoundaryFormula_sample_prefix_five
    W X hb hε hεW hεone hflow
  let slopeData := n04PositiveGeometry_rootBoundaryInput_sample_prefix_eight
    W X hb hε hεW hεone hflow
  let Bo : ℕ := oddData.choose
  let Be : ℕ := evenData.choose
  let Bb : ℕ := slopeData.choose
  let low : ℕ := max Bo (max Be Bb)
  have hBo : Bo ≤ low := le_max_left _ _
  have hBe : Be ≤ low := (le_max_left _ _).trans (le_max_right _ _)
  have hBb : Bb ≤ low := (le_max_right _ _).trans (le_max_right _ _)
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨low, oddData.choose_spec.1.trans hBo, fun K => ?_⟩
  let oddShift := oddData.choose_spec.2 (2 / 3 : ℝ) K
  let evenShift := evenData.choose_spec.2 K
  let slopeShift := slopeData.choose_spec.2 K
  let co : ℕ := oddShift.choose
  let ce : ℕ := evenShift.choose
  let cb : ℕ := slopeShift.choose
  let shift : ℕ := max co (max ce cb)
  have hco : co ≤ shift := le_max_left _ _
  have hce : ce ≤ shift := (le_max_left _ _).trans (le_max_right _ _)
  have hcb : cb ≤ shift := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨shift, fun s => ?_⟩
  let oddOrder := oddShift.choose_spec (s + (shift - co) * K)
  let evenOrder := evenShift.choose_spec (s + (shift - ce) * K)
  let slopeOrder := slopeShift.choose_spec (s + (shift - cb) * K)
  let Ao : ℝ := oddOrder.choose
  let Ae : ℝ := evenOrder.choose
  let Ab : ℝ := slopeOrder.choose
  let B : ℝ := max Ao (max Ae Ab)
  have hB : 1 ≤ B := oddOrder.choose_spec.1.trans (le_max_left _ _)
  have hAo : Ao ≤ B := le_max_left _ _
  have hAe : Ae ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hAb : Ab ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let κ : ℝ := (3 / 2 : ℝ) ^ (2 / 3 : ℝ)
  let packData := coefficientEnvelope_pack ((2 : ℝ) ^ 4 * (1 + 4 * |κ|) * B) B
  let A₀ : ℝ := packData.choose
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx n hn hn4 Q z hz hzlow θ R hR hzR
  let g : ℝ → ℝ := hctx.choose
  let ρ : ℝ := hctx.choose_spec.choose
  let hρ : 0 < ρ := hctx.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  have href := (hc.2.2.2.2 (W.C.referenceState, 0)
    hN.reference_mem_stateNeighborhood hN.2.2.1.stateSector).1
  have hstrip (x : StateDirections W.S × ℝ) (hx : x ∈ sectorNeighborhood W.S base ε ε) :=
    (hc.2.2.2.2 (liftSectorParameter W.S W.C x)
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x)).1
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M : ℝ := B * E ^ B
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P : (StateDirections W.S × ℝ) → Prop := fun v =>
    p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hP : P 0 := ⟨((p low).map_zero').trans_le zero_le_one,
    ((p (low + s + shift * K + 1)).map_zero').trans_le (zero_le_one.trans hR)⟩
  have hcost {a : ℝ} (ha : a ≤ B) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hlo (b : ℕ) (hb : b ≤ low) (x : StateDirections W.S × ℝ) (hx : p low x ≤ 1) :
      p b x ≤ 1 := (hp hb x).trans hx
  have hhi (b c : ℕ) (hb : b ≤ low) (hc : c ≤ shift)
      (x : StateDirections W.S × ℝ) (hx : p (low + s + shift * K + 1) x ≤ R) :
      p (b + (s + (shift - c) * K) + c * K + 1) x ≤ R := by
    apply (hp ?_ x).trans hx
    have he := n04PositiveGeometry_prefix_horizon s K c shift hc
    omega
  have hraise (a : ℝ) (ha : a ≤ B) (c : ℕ) (hc : c ≤ shift) (u k : ℕ) :
      a * E ^ a * parameterHeightWeight H k *
          R ^ (((u + c * k : ℕ) : ℝ) /
            (((s + (shift - c) * K + c * K : ℕ) : ℝ) + 1)) ≤
        M * parameterHeightWeight H k * t ^ (u + shift * k) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcost ha) (parameterHeightWeight_nonneg hH k))
      (n04PositiveGeometry_prefix_power_align s K u k c shift hc hR)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH k))
  have hO (j : ℕ) (hj : j ≤ 3)
      (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_rootOddPowerTrace W.D W.S W.C g m (!side) (2 / 3 : ℝ) j)) :
      N04BoundaryWordBounds J K s 5 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular J (smoothDirections_angularStateSlice J)
      K s 5 z hz θ P M H t shift
    intro k hk u hu d hd v hv
    have hraw := oddOrder.choose_spec.2 i side m hm g hc.1 hc.2.1 hc.2.2.1
      ρ hρ href hstrip j hj k hk u (hu.trans (Nat.le_add_right _ _)) d hd θ
      (smoothDirections_angularStateSlice J (u + d) θ) z hz (hlo Bo hBo z hzlow) v
      (fun l => hlo Bo hBo (v l) (hv l).1) R hR (hhi Bo co hBo hco z hzR)
      (fun l => hhi Bo co hBo hco (v l) (hv l).2)
    exact hraw.trans (hraise Ao hAo co hco u k)
  have hEtrace (j : Fin 8)
      (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_rootBoundaryFormula W.D W.S W.C g m (!side) j)) :
      N04BoundaryWordBounds J K s 5 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular J (smoothDirections_angularStateSlice J)
      K s 5 z hz θ P M H t shift
    intro k hk u hu d hd v hv
    have hraw := evenOrder.choose_spec.2 i side m hm g hc.1 hc.2.1 hc.2.2.1
      ρ hρ href j k hk u (hu.trans (Nat.le_add_right _ _)) d hd θ
      (smoothDirections_angularStateSlice J (u + d) θ) z hz (hlo Be hBe z hzlow) v
      (fun l => hlo Be hBe (v l) (hv l).1) R hR (hhi Be ce hBe hce z hzR)
      (fun l => hhi Be ce hBe hce (v l) (hv l).2)
    exact hraw.trans (hraise Ae hAe ce hce u k)
  have hBtrace (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryInput W.D W.S W.C g m (!side) 8)) :
      N04BoundaryWordBounds J K s 5 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular J (smoothDirections_angularStateSlice J)
      K s 5 z hz θ P M H t shift
    intro k hk u hu d hd v hv
    have hraw := slopeOrder.choose_spec.2 i side m hm g hc.1 hc.2.1 hc.2.2.1
      ρ hρ href 8 k hk u (hu.trans (Nat.le_add_right _ _)) d (hd.trans (by decide)) θ
      (smoothDirections_angularStateSlice J (u + d) θ) z hz (hlo Bb hBb z hzlow) v
      (fun l => hlo Bb hBb (v l) (hv l).1) R hR (hhi Bb cb hBb hcb z hzR)
      (fun l => hhi Bb cb hBb hcb (v l) (hv l).2)
    exact hraw.trans (hraise Ab hAb cb hcb u k)
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  have hout := n04PositiveGeometry_storedForwardJet_word_bound W.hT W.hS hN hεone hflow
    hctx hr hroot n hn hn4 Q hz hP (zero_le_one.trans hM) hH ht hO hEtrace hBtrace
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    (2 : ℝ) ^ n * ((1 + 4 * |κ|) * M) ≤ (2 : ℝ) ^ 4 * ((1 + 4 * |κ|) * M) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn4)
        (mul_nonneg (by positivity) (zero_le_one.trans hM))
    _ = ((2 : ℝ) ^ 4 * (1 + 4 * |κ|) * B) * E ^ B := by dsimp only [M]; ring
    _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
    _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
