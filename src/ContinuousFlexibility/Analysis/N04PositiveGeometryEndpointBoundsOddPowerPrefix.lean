import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddTraces

/-!
# The sampled prefix of the actual odd-coefficient powers

The common low order includes the already proved reciprocal bound for
the true zeroth odd coefficient. All later parameter orders use the
same domain and retain the reserved angular derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04PositiveOddPowerPrefixStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootOddPowerTrace_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ γ : ℝ, ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
      ∀ ρ : ℝ, 0 < ρ →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) ρ →
      (∀ z ∈ sectorNeighborhood W.S base ε ε,
        RootCoefficientStripConditions W.D.w g
          (stateProfile W.D W.S W.C (liftSectorParameter W.S W.C z).1)
          (stateHeight W.D W.S W.C (liftSectorParameter W.S W.C z))
          (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) ρ) →
      ∀ n : ℕ, n ≤ 3 → ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ d : ℕ, d ≤ 1 →
      ∀ θ : ℝ, ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => iteratedDeriv (u + d)
          (fun η => n04PositiveGeometry_rootOddPowerTrace W.D W.S W.C g m (!side) γ n
            (z, η)) θ),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ l, pairGrading (sectorGrading W.S) realGrading low (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      (∀ l, pairGrading (sectorGrading W.S) realGrading
        (low + s + shift * K + 1) (v l) ≤ R) →
      ‖J.D k z v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine (n04PositiveGeometry_rootBoundaryFormula_sample_prefix
    W X hb hε hεW hεone hflow).elim fun Bf h => ?_
  refine h.elim fun hBf hf => ?_
  refine (n04PositiveGeometry_rootOddValue_sample_inverse
    W X hb hε hεW hflow).elim fun Bi h => ?_
  refine h.elim fun hBi h => ?_
  refine h.elim fun Ci h => ?_
  refine h.elim fun hCi hi => ?_
  obtain ⟨RH, hRH, hheight⟩ := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 RH
  have hL : 1 ≤ L := le_max_left _ _
  let low := max Bf Bi
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨low, hBf.trans (le_max_left _ _), fun γ K => ?_⟩
  refine (hf K).elim fun shift hshift => ?_
  refine ⟨shift, fun s => ?_⟩
  refine (hshift s).elim fun Af h => ?_
  refine h.elim fun hAf hformula => ?_
  let B := max Af (max Ci L)
  have hB : 1 ≤ B := hAf.trans (le_max_left _ _)
  have hAfB : Af ≤ B := le_max_left _ _
  have hCiB : Ci ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hLB : L ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  choose C hC degree hpower using fun j : Fin 4 =>
    n04PositiveGeometry_rootPowerTrace_word_bound (E := StateDirections W.S × ℝ)
      γ j.val (K + s + 1) L hL
  let C₀ : ℝ := 1 + ∑ j, C j
  let D : ℕ := ∑ j, degree j
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => zero_le_one.trans (hC j))
  have hCC (j : Fin 4) : C j ≤ C₀ :=
    (Finset.single_le_sum (fun l _ => zero_le_one.trans (hC l)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hDD (j : Fin 4) : degree j ≤ D :=
    Finset.single_le_sum (fun l _ => Nat.zero_le (degree l)) (Finset.mem_univ j)
  obtain ⟨A₀, _, hpack⟩ := coefficientEnvelope_pack (C₀ * B ^ D) (B * D)
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm g hg hg0 hfactor ρ hρ href hstrip n hn k hk u hu d hd θ J z hz hzlow v hv R hR hzR hvR
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M : ℝ := B * E ^ B
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P : (StateDirections W.S × ℝ) → Prop := fun w =>
    p low w ≤ 1 ∧ p (low + s + shift * K + 1) w ≤ R
  have hP : P 0 := by
    constructor
    · simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
    · simpa only [map_zero] using (zero_le_one.trans hR)
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hHL : H ≤ L := (hheight i).2.trans (le_max_right _ _)
  have hMB : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hMB
  have hHM : H ≤ M := hHL.trans (hLB.trans hMB)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (a : ℕ) : t ^ a =
      R ^ ((a : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  have hcost {C : ℝ} (hC : C ≤ B) : C * E ^ C ≤ M :=
    mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hE hC)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := by
    rw [hrad]
    exact (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := by
    rw [hrad]
    exact (W.roots i side).2.1
  let f := n04PositiveGeometry_rootOddTrace W.D W.S W.C g m (!side)
  let JO (j : ℕ) (hj : j ≤ n) : SmoothDirections
      (sectorNeighborhood W.S base ε ε ×ˢ univ) (f j) :=
    n04PositiveGeometry_rootOddTrace_joint W.hT W.hS hN hεone
      g hg hg0 m (!side) hr hroot j (hj.trans hn)
  have hpos : ∀ y ∈ sectorNeighborhood W.S base ε ε ×ˢ (univ : Set ℝ), 0 < f 0 y := by
    intro y hy
    exact n04PositiveGeometry_rootOddTrace_zero_pos W.hT W.hS hN hflow
      g m (!side) hρ hy.1 (hstrip y.1 hy.1) y.2
  let JP := n04PositiveGeometry_rootPowerTrace_joint
    (sectorNeighborhood_isOpen W.S base ε ε) JO γ hpos
  have hinv : (f 0 (z, θ))⁻¹ ≤ M := by
    have h := (hi i side m hm g hg hfactor z hz
      ((hp (le_max_right Bf Bi) z).trans hzlow) ρ hρ (hstrip z hz) θ).2
    exact h.trans (hcost hCiB)
  have hinput (j : ℕ) (hj : j ≤ n) :
      N04BoundaryWordBounds (JO j hj) K s 1 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular (JO j hj)
      (smoothDirections_angularStateSlice (JO j hj)) K s 1 z hz θ P M H t shift
    intro e he b hbs a ha w hw
    let Q := smoothDirections_angularStateSlice (JO j hj) (b + a) θ
    let QF := Q.congr (fun y _ => congrArg
      (fun f : ℝ → ℝ => iteratedDeriv (b + a) f θ)
      (funext fun η => congrFun
        (n04PositiveGeometry_rootOddTrace_eq W.D W.S W.C g m (!side) j (hj.trans hn))
          (y, η)))
    have hh := hformula i side m hm g hg hg0 hfactor ρ hρ href
      ⟨4 + j, by omega⟩ e he b hbs a ha θ QF z hz
      ((hp (le_max_left Bf Bi) z).trans hzlow) w
      (fun l => (hp (le_max_left Bf Bi) (w l)).trans (hw l).1) R hR
      ((hp (by dsimp only [low]; omega : Bf + s + shift * K + 1 ≤
        low + s + shift * K + 1) z).trans hzR)
      (fun l => (hp (by dsimp only [low]; omega : Bf + s + shift * K + 1 ≤
        low + s + shift * K + 1) (w l)).trans (hw l).2)
    rw [htpow]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcost hAfB) (parameterHeightWeight_nonneg hH e))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
  let idx : Fin 4 := ⟨n, by omega⟩
  have hout := hpower idx (sectorNeighborhood_isOpen W.S base ε ε) JO JP hpos
    K s 1 le_rfl z hz θ P M H t hM hH hHM hHL ht shift hinput hinv
  have hnorm := n04PositiveGeometry_boundaryWord_to_angular_reserve JP
    (smoothDirections_angularStateSlice JP) hz θ P hP hout
      k (u + d) hk (by omega) v (fun l => ⟨hv l, hvR l⟩)
  have hpoly : C idx * M ^ degree idx ≤ A * E ^ A := by
    calc
      _ ≤ C₀ * M ^ D := mul_le_mul (hCC idx) (pow_le_pow_right₀ hM (hDD idx))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC₀)
      _ = (C₀ * B ^ D) * E ^ (B * D) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
        ring
      _ ≤ A₀ * E ^ A₀ := hpack E hE
      _ ≤ A * E ^ A := mul_le_mul hA₀A
        (Real.rpow_le_rpow_of_exponent_le hE hA₀A)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hpow : t ^ ((u + d - 1) + shift * k) ≤ t ^ (u + shift * k) :=
    pow_le_pow_right₀ ht (by omega)
  have heq := J.unique (smoothDirections_angularStateSlice JP (u + d) θ) k z hz
  have hnorm' := (congrArg norm (congrArg
    (fun A : (StateDirections W.S × ℝ) [×k]→L[ℝ] ℝ => A v) heq)).trans_le hnorm
  have hfinal := hnorm'.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hpoly (parameterHeightWeight_nonneg hH k)) hpow
    (pow_nonneg (zero_le_one.trans ht) _)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) (parameterHeightWeight_nonneg hH k)))
  simpa only [htpow] using hfinal

end ContinuousFlexibility.Analysis
