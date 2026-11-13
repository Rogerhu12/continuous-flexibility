import ContinuousFlexibility.Analysis.N01RootInverseCoordinateAxisMaterialJets
import ContinuousFlexibility.Analysis.RootOddAxisJets
import ContinuousFlexibility.Analysis.RootChartExtension
import ContinuousFlexibility.Analysis.RootChartSymmetry

/-!
# Material jets of the genuine even and odd root extensions

The same normalized actual inverse coordinate supplies both extensions.
Only its angular displacement is used at order zero. The odd coefficient
costs one source derivative, uniformly before the component and state;
neither the localization radius nor the parameter scale enters the cost.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem exists_extendedRootEvenOdd_axis_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) →
      ∀ θ M : ℝ, 1 ≤ M →
      (∀ k, k ≤ n + 1 →
        ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ × ℝ => G q - q.2.2) (0, 0, θ)‖ ≤ M) →
      ‖iteratedFDeriv ℝ n (fun p : PolarPoint => extendedRootEven G p - p.2)
        (0, θ)‖ ≤ C * M ∧
      ‖iteratedFDeriv ℝ n (extendedRootOddCoefficient G) (0, θ)‖ ≤ C * M := by
  obtain ⟨CE, hCE, heven⟩ := exists_rootEven_axis_jet_bound n
  obtain ⟨CO, hCO, hodd⟩ := exists_rootOddCoefficient_axis_jet_bound n
  let C : ℝ := CE + 2 * CO
  have hC : 0 < C := by dsimp only [C]; linarith only [hCE, hCO]
  refine ⟨C, hC, ?_⟩
  intro G hG hperiod θ M hM hinput
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hdisp : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => G q - q.2.2) :=
    hG.sub contDiff_snd.snd
  have hextEven : ContDiff ℝ ∞ (extendedRootEven G) :=
    contDiff_extendedRootEven hG Real.pi_ne_zero
      (fun x _ θ => rootEven_period_add hperiod x θ)
  have hextOdd : ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
    contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero
      (fun x _ => rootOddCoefficient_periodic hperiod x)
  have heq : EqOn (fun p : PolarPoint => extendedRootEven G p - p.2)
      (rootEven (fun q : ℝ × ℝ × ℝ => G q - q.2.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    change extendedRootEven G p - p.2 =
      rootEven (fun q : ℝ × ℝ × ℝ => G q - q.2.2) p
    rw [extendedRootEven_of_nonneg G hp.1.le]
    dsimp only [rootEven]
    ring
  have hevenBound := heven (fun q : ℝ × ℝ × ℝ => G q - q.2.2) hdisp
    (fun p : PolarPoint => extendedRootEven G p - p.2)
    (hextEven.sub contDiff_snd) heq θ M
    (fun k hk => hinput k (hk.trans (Nat.le_succ n)))
  let π : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hπnorm : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa only [π, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      one_mul] using (norm_snd_le q.2).trans (norm_snd_le q)
  have hpositive (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
      ‖iteratedFDeriv ℝ k G (0, 0, θ)‖ ≤ 2 * M := by
    have hπjet : ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ × ℝ => q.2.2)
        (0, 0, θ)‖ ≤ 1 :=
      (flowJet_norm_iteratedFDeriv_clm_le π hk (0, 0, θ)).trans hπnorm
    have he : G = (fun q : ℝ × ℝ × ℝ => G q - q.2.2) +
        (fun q : ℝ × ℝ × ℝ => q.2.2) := by funext q; simp
    rw [he, iteratedFDeriv_add_apply
      (hdisp.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
      ((contDiff_snd.snd : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.2)).contDiffAt.of_le
        (by simp : (k : ℕ∞ω) ≤ ∞))]
    exact ((norm_add_le _ _).trans (add_le_add (hinput k hkn) hπjet)).trans
      (by linarith only [hM])
  have hoddEq : EqOn (extendedRootOddCoefficient G) (fun p => -rootOdd G p)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    rw [extendedRootOddCoefficient_of_nonneg G hp.1.le]
    rfl
  have hoddBound := hodd G hG (extendedRootOddCoefficient G) hextOdd hoddEq θ
    (2 * M) hpositive
  constructor
  · exact hevenBound.trans (mul_le_mul_of_nonneg_right
      (show CE ≤ C by dsimp only [C]; linarith only [hCO]) hM0)
  · calc
      _ ≤ CO * (2 * M) := hoddBound
      _ = (2 * CO) * M := by ring
      _ ≤ C * M := mul_le_mul_of_nonneg_right
        (by dsimp only [C]; linarith only [hCE]) hM0

theorem n01_rootEvenOdd_unit_axis_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ x, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * x) = x * g x) →
      ∀ R : ℝ, ∀ hR : 0 < R,
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R →
      ∀ δ : ℝ, δ ≠ 0 → ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z) δ) Θ →
      ∀ θ : ℝ, ∀ n : ℕ,
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        ‖iteratedFDeriv ℝ n (fun p : PolarPoint => extendedRootEven G p - p.2)
          (0, θ)‖ ≤ B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) ∧
        ‖iteratedFDeriv ℝ n (extendedRootOddCoefficient G) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  classical
  choose DC hDC hbound using exists_extendedRootEvenOdd_axis_jet_bound
  obtain ⟨C0, low, inputLoss, hC0, hfloor, B0, hB0, hroot⟩ :=
    n01_rootInverseCoordinate_unit_axis_material_jets_of_component_optical
      hS hT hN hflow hK
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  let A : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 2), B0 k
  have hA (n : ℕ) : 1 ≤ A n :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => (hB0 k).le))
  have hCA (n : ℕ) : 0 < DC n * A n :=
    mul_pos (hDC n) (zero_lt_one.trans_le (hA n))
  let B : ℕ → ℝ := fun n => 1 + A n + DC n * A n
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith only [hA n, hCA n]
  refine ⟨C0, low, inputLoss + 1, hC0, hfloor, B, hB, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ n
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  let P : ℝ := 1 + pairGrading (stateGrading S) realGrading
    (n + (inputLoss + 1)) (z - (C.referenceState, 0))
  have hP : 1 ≤ P := le_add_of_nonneg_right (apply_nonneg _ _)
  let M : ℝ := A n * W ^ (A n) * P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hA n)
      (Real.one_le_rpow hW (zero_le_one.trans (hA n)))) hP
  let r : ℝ := n01ComponentRoot C m side
  let σ : ℝ := n01ComponentRootOrientation side
  let d : PolarPoint → ℝ := localizedRootDrift D S C r σ hR z
  let c : PolarPoint → ℝ := localizedRootSpeed D S C g r σ hR z
  let Θ₁ : (ℝ × ℝ) → ℝ → ℝ → ℝ := rootFlowParameterUnscale Θ δ
  let l : ℝ → ℝ := n01RootLabel S C z m side
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ₁ l
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hfield := contDiff_rootRegularizedField hregular.1 hregular.2
  have hfieldPeriod := rootRegularizedField_periodic hperiod.1 hperiod.2
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ₁ q.1 1 q.2) :=
    n04Flow_contDiff_slice hfield hfieldPeriod hΘ₁ ht
  have hpositive : ∀ p θ, 0 < deriv (fun η => Θ₁ p 1 η) θ :=
    fun p θ => n04Flow_angular_deriv_pos hfield hfieldPeriod hΘ₁ ht p θ
  have hendpointPeriod : ∀ p θ, Θ₁ p 1 (θ + Real.pi) = Θ₁ p 1 θ + Real.pi :=
    fun p θ => n04Flow_period_add hfield hfieldPeriod hΘ₁ p θ ht
  have hG : ContDiff ℝ ∞ G := contDiff_rootInverseCoordinate Real.pi_ne_zero
    hEndpoint hpositive hendpointPeriod (n01RootLabel_contDiff hS hT hN hz hs m side)
  have hGperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi :=
    rootInverseCoordinate_period_add Real.pi_ne_zero hEndpoint hpositive hendpointPeriod
      (n01RootLabel_period_add hN hz hs m side)
  have hprefix (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ × ℝ => G q - q.2.2) (0, 0, θ)‖ ≤ M := by
    have hb : ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ × ℝ => G q - q.2.2)
        (0, 0, θ)‖ ≤ B0 k * W ^ (B0 k) *
        (1 + pairGrading (stateGrading S) realGrading (k + inputLoss)
          (z - (C.referenceState, 0))) :=
      hroot z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip
        δ hδ Θ hΘ θ k
    have hcoef : B0 k ≤ A n :=
      (Finset.single_le_sum (fun i _ => (hB0 i).le)
        (Finset.mem_range.mpr (by omega : k < n + 2))).trans
        (le_add_of_nonneg_left zero_le_one)
    exact hb.trans (mul_le_mul
      (mul_le_mul hcoef (Real.rpow_le_rpow_of_exponent_le hW hcoef)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans (hA n)))
      (add_le_add_left (hp (by omega : k + inputLoss ≤ n + (inputLoss + 1)) _) 1)
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg (zero_le_one.trans (hA n))
        (Real.rpow_nonneg (zero_le_one.trans hW) _)))
  have hjets := hbound n G hG hGperiod θ M hM hprefix
  have hAB : A n ≤ B n := by dsimp only [B]; linarith only [hCA n]
  have hCAB : DC n * A n ≤ B n := by dsimp only [B]; linarith only [hA n]
  have hmajorant : DC n * M ≤ B n * W ^ (B n) * P := by
    calc
      _ = (DC n * A n) * W ^ (A n) * P := by dsimp only [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hCAB (Real.rpow_le_rpow_of_exponent_le hW hAB)
          (Real.rpow_nonneg (zero_le_one.trans hW) _) (hB n).le)
        (zero_le_one.trans hP)
  exact ⟨hjets.1.trans hmajorant, hjets.2.trans hmajorant⟩

end ContinuousFlexibility.Analysis
