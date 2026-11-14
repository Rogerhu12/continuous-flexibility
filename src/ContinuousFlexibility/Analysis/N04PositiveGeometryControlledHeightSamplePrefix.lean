module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightTrace
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerPrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootRadicandPower

/-!
# Sampled bounds for the actual height traces

The low base precedes the real exponent and every derivative budget.
The two parameter-dependent factors retain the same height weight and
five angular orders; the remaining factor consists of fixed reference
radial derivatives at the same positive endpoint sample.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_rootHeightPowerTrace_sample_prefix
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
      ∀ n : ℕ, n ≤ 3 →
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_rootHeightPowerTrace W.D W.S W.C g m (!side) γ n),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds J K s 5 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  classical
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let oddData := n04PositiveGeometry_rootOddPowerTrace_sample_prefix_five
    W X hb hε hεW hεone hflow
  let Bo := oddData.choose
  have hBo : base ≤ Bo := oddData.choose_spec.1
  let discData := n04PositiveGeometry_rootDiscPower_sample_prefix W X hb hε hεW hεone
  let Bd := discData.choose
  let low := max Bo Bd
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 heightData.choose
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨low, hBo.trans (le_max_left _ _), fun γ K => ?_⟩
  let shiftData := oddData.choose_spec.2 (γ / 6) K
  let shift := shiftData.choose
  refine ⟨shift, fun s => ?_⟩
  let oddOrder := shiftData.choose_spec s
  let Ao := oddOrder.choose
  let discOrder := discData.choose_spec.2 (γ / 2) K shift s
  let Ad := discOrder.choose
  let refOrder := n04PositiveGeometry_referenceRootRadicandPower_sample_prefix W X (-γ / 4) 3
  let Ar := refOrder.choose
  let c : ℝ := (3 / 2 : ℝ) ^ (γ / 6)
  let B := max Ao (max Ad (max Ar (|c| * Ar)))
  have hB : 1 ≤ B := oddOrder.choose_spec.1.trans (le_max_left _ _)
  have hAoB : Ao ≤ B := le_max_left _ _
  have hAdB : Ad ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hArB : Ar ≤ B := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hcArB : |c| * Ar ≤ B := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let N := K + s + 5
  let productData (j : Fin 4) :=
    n04PositiveGeometry_rootHeightProductTrace_word_bound
      (E := StateDirections W.S × ℝ) j.val N L hL
  let C : Fin 4 → ℝ := fun j => (productData j).choose
  have hC (j : Fin 4) : 1 ≤ C j := (productData j).choose_spec.1
  let C₀ : ℝ := 1 + ∑ j, C j
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hC j)))
  have hCC (j : Fin 4) : C j ≤ C₀ :=
    (Finset.single_le_sum (fun l _ => zero_le_one.trans (hC l)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let packData := coefficientEnvelope_pack (C₀ * B ^ (N + 3)) (B * ((N + 3 : ℕ) : ℝ))
  let A₀ := packData.choose
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm g hg hg0 hfactor ρ hρ href hstrip n hn J z hz hzlow θ R hR hzR
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P : (StateDirections W.S × ℝ) → Prop := fun v =>
    p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHL : H ≤ L := (heightData.choose_spec.2 i).2.trans (le_max_right _ _)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {Q : ℝ} (hQ : Q ≤ B) : Q * E ^ Q ≤ M :=
    mul_le_mul hQ (Real.rpow_le_rpow_of_exponent_le hE hQ)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have htpow (b : ℕ) : t ^ b =
      R ^ ((b : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := by
    rw [hrad]; exact (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := by
    rw [hrad]; exact (W.roots i side).2.1
  let JO (j : ℕ) (hj : j ≤ n) := n04PositiveGeometry_rootOddPowerTrace_joint
    W.hT W.hS hN hεone hflow g hg hg0 m (!side) hr hroot hρ hstrip (γ / 6) j (hj.trans hn)
  let JD (j : ℕ) (_ : j ≤ n) := n04PositiveGeometry_rootDiscPowerTrace_joint
    W.hT W.hS hN hεone hr hroot (γ / 2) (n01ComponentRootOrientation (!side)) j
  have ho (j : ℕ) (hj : j ≤ n) :
      N04BoundaryWordBounds (JO j hj) K s 5 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular (JO j hj)
      (smoothDirections_angularStateSlice (JO j hj)) K s 5 z hz θ P M H t shift
    intro k hk b hb d hd v hv
    have hraw := oddOrder.choose_spec.2 i side m hm g hg hg0 hfactor ρ hρ href hstrip
      j (hj.trans hn) k hk b hb d hd θ
      (smoothDirections_angularStateSlice (JO j hj) (b + d) θ) z hz
      ((hp (le_max_left Bo Bd) z).trans hzlow) v
      (fun l => (hp (le_max_left Bo Bd) (v l)).trans (hv l).1) R hR
      ((hp (by dsimp only [low]; omega : Bo + s + shift * K + 1 ≤
        low + s + shift * K + 1) z).trans hzR)
      (fun l => (hp (by dsimp only [low]; omega : Bo + s + shift * K + 1 ≤
        low + s + shift * K + 1) (v l)).trans (hv l).2)
    exact (hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcost hAoB) (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))).trans_eq
      (congrArg (fun q : ℝ => M * parameterHeightWeight H k * q) (htpow (b + shift * k)).symm)
  have hd (j : ℕ) (hj : j ≤ n) :
      N04BoundaryWordBounds (JD j hj) K s 5 z θ P M H t shift := by
    apply n04PositiveGeometry_boundaryWord_of_angular (JD j hj)
      (smoothDirections_angularStateSlice (JD j hj)) K s 5 z hz θ P M H t shift
    intro k hk b hb d hd v hv
    have hraw := discOrder.choose_spec.2 i side m hm j (hj.trans hn) d hd b hb θ
      (smoothDirections_angularStateSlice (JD j hj) (b + d) θ) k hk z hz
      ((hp (le_max_right Bo Bd) z).trans hzlow) v
      (fun l => (hp (le_max_right Bo Bd) (v l)).trans (hv l).1) R hR
      ((hp (by dsimp only [low]; omega : Bd + s + shift * K + 1 ≤
        low + s + shift * K + 1) z).trans hzR)
      (fun l => (hp (by dsimp only [low]; omega : Bd + s + shift * K + 1 ≤
        low + s + shift * K + 1) (v l)).trans (hv l).2)
    exact (hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcost hAdB) (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))).trans_eq
      (congrArg (fun q : ℝ => M * parameterHeightWeight H k * q) (htpow (b + shift * k)).symm)
  have ha (j : ℕ) (hj : j ≤ n) :
      |c * iteratedDeriv j (fun t => rootProfileRadicand W.D.w g
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) t ^ (-γ / 4)) 0|
        ≤ M := by
    rw [abs_mul]
    have hjets := refOrder.choose_spec.2 i side m hm g hg hfactor ρ hρ href j (hj.trans hn)
    calc
      _ ≤ |c| * (Ar * E ^ Ar) := mul_le_mul_of_nonneg_left hjets (abs_nonneg c)
      _ = (|c| * Ar) * E ^ Ar := by ring
      _ ≤ B * E ^ B := mul_le_mul hcArB (Real.rpow_le_rpow_of_exponent_le hE hArB)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  let idx : Fin 4 := ⟨n, by omega⟩
  have hout := (productData idx).choose_spec.2
    (sectorNeighborhood_isOpen W.S base ε ε) _ JO JD J K s 5 le_rfl z hz θ P
    M H t hM hH hHL ht shift ha ho hd
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    C idx * M ^ (N + 3) ≤ C₀ * M ^ (N + 3) :=
      mul_le_mul_of_nonneg_right (hCC idx) (pow_nonneg (zero_le_one.trans hM) _)
    _ = (C₀ * B ^ (N + 3)) * E ^ (B * ((N + 3 : ℕ) : ℝ)) := by
      dsimp only [M]
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
      ring
    _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
    _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
