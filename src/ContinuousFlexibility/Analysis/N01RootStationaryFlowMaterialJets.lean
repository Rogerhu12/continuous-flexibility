import ContinuousFlexibility.Analysis.N01RootSpeedPowerMaterialJets
import ContinuousFlexibility.Analysis.N01RootFieldLocalization
import ContinuousFlexibility.Analysis.RootFlowParameterUnscale
import ContinuousFlexibility.Analysis.RootStationaryInverseMaterialJets

/-!
# The same actual root flow with uniform zero-axis material costs

The localized fields have exactly the original jets at the root, at
every order. The already chosen scaled flow is then reparametrized to
unit scale. Its forward and actual circle-inverse jets follow from the
stationary ODE estimates. No inverse model radius or normalization scale
is charged. The raw optical lower remains an explicit same-witness input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_rootFlow_unit_axis_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hK : 0 < K) :
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
      ∀ θ : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n →
        let f : N04FlowPoint → ℝ :=
          fun y => rootFlowParameterUnscale Θ δ y.1 t y.2
        ‖iteratedFDeriv ℝ n f ((0, 0), θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) ∧
        ‖iteratedFDeriv ℝ n (parameterizedCircleInverse f) ((0, 0), θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨CD, lowD, lossD, hCD, hfloorD, BD, hBD, hjetsD⟩ :=
    n01_orientedRootDrift_axis_material_jets hS hT hN
  obtain ⟨CC, lowC, lossC, hCC, hfloorC, hpowersC⟩ :=
    n01_rootSpeed_axis_rpow_material_jets_of_component_optical hS hT hN hK
  obtain ⟨BC, hBC, hjetsC⟩ := hpowersC (1 : ℝ)
  let C0 := max CD CC
  have hC0 : 1 ≤ C0 := hCD.trans (le_max_left _ _)
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorD j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ((hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1.le))
  let inputLoss := max lossD lossC
  let A : ℕ → ℝ := fun n => max 1 (max (BD n) (BC n))
  have hA (n : ℕ) : 1 ≤ A n := le_max_left _ _
  have hDA (n : ℕ) : BD n ≤ A n := (le_max_left _ _).trans (le_max_right _ _)
  have hCA (n : ℕ) : BC n ≤ A n := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨flowLow, flowLoss, hflow⟩ :=
    rootRegularizedFlow_zero_positiveJets_le_material hp hI inputLoss
  obtain ⟨inverseLow, inverseLoss, hinverse⟩ :=
    rootRegularizedFlow_zero_inverseJets_le_material hp hI inputLoss
  obtain ⟨BF, hBF, hforward⟩ := hflow A hA
  obtain ⟨BI, hBI, hbackward⟩ := hinverse A hA
  let B : ℕ → ℝ := fun n => max 1 (max (BF (n - 1)) (BI n))
  have hB (n : ℕ) : 0 < B n := zero_lt_one.trans_le (le_max_left _ _)
  let low := max lowD (max lowC (max flowLow inverseLow))
  let outLoss := max flowLoss inverseLoss
  refine ⟨C0, low, outLoss, hC0, hsample, B, hB, ?_⟩
  intro z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ t ht n hn
  have hzD := (hp (le_max_left lowD (max lowC (max flowLow inverseLow))) _).trans hzlow
  have hzC := (hp ((le_max_left lowC (max flowLow inverseLow)).trans
    (le_max_right lowD (max lowC (max flowLow inverseLow)))) _).trans hzlow
  have hzF := (hp ((le_max_left flowLow inverseLow).trans
    ((le_max_right lowC (max flowLow inverseLow)).trans
      (le_max_right lowD (max lowC (max flowLow inverseLow))))) _).trans hzlow
  have hzI := (hp ((le_max_right flowLow inverseLow).trans
    ((le_max_right lowC (max flowLow inverseLow)).trans
      (le_max_right lowD (max lowC (max flowLow inverseLow))))) _).trans hzlow
  let W := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hsample j
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hWD : CD * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
  have hWC : CC * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
  have hpack {a b V : ℝ} {k l l' : ℕ}
      (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 ≤ b)
      (hV : 1 ≤ V) (hVW : V ≤ W) (hll' : l ≤ l') :
      a * V ^ a * (1 + pairGrading (stateGrading S) realGrading (k + l)
        (z - (C.referenceState, 0))) ≤
      b * W ^ b * (1 + pairGrading (stateGrading S) realGrading (k + l')
        (z - (C.referenceState, 0))) := by
    have hpower : V ^ a ≤ W ^ b :=
      (Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
        (Real.rpow_le_rpow_of_exponent_le hW hab)
    exact mul_le_mul
      (mul_le_mul hab hpower (Real.rpow_nonneg (zero_le_one.trans hV) _) hb)
      (add_le_add_left (hp (Nat.add_le_add_left hll' k) _) 1)
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg hb (Real.rpow_nonneg (zero_le_one.trans hW) _))
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hzero : |((0, θ) : PolarPoint).1| ≤ R / 4 := by
    simpa only [abs_zero] using (div_pos hR (by norm_num : (0 : ℝ) < 4)).le
  have hlocal (k : ℕ) :=
    iteratedFDeriv_localizedRootFields_eq D S C g r σ hR z k (q := (0, θ)) hzero
  have hdb (k : ℕ) : ‖iteratedFDeriv ℝ k d (0, θ)‖ ≤
      A k * W ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
        (k + inputLoss) (z - (C.referenceState, 0))) := by
    dsimp only [d]
    rw [(hlocal k).1]
    exact ((hjetsD z hz hs hzD m j hhost side θ).2 k).trans
      (hpack (hBD k).le (hDA k) (zero_le_one.trans (hA k))
        (hfloorD j) hWD (le_max_left lossD lossC))
  have hcb (k : ℕ) : ‖iteratedFDeriv ℝ k c (0, θ)‖ ≤
      A k * W ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
        (k + inputLoss) (z - (C.referenceState, 0))) := by
    dsimp only [c]
    rw [(hlocal k).2]
    have hb := hjetsC z hz hs hzC m j hhost hoptical side g hg hfactor R hR hstrip θ k
    have hb' : ‖iteratedFDeriv ℝ k
        (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) (0, θ)‖ ≤
        BC k * (CC * T.E0 (T.sample j)) ^ (BC k) *
          (1 + pairGrading (stateGrading S) realGrading (k + lossC)
            (z - (C.referenceState, 0))) := by
      simpa only [Real.rpow_one] using hb
    exact hb'.trans (hpack (hBC k).le (hCA k) (zero_le_one.trans (hA k))
      (hfloorC j) hWC (le_max_right lossD lossC))
  let Θ₁ := rootFlowParameterUnscale Θ δ
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  have hf := hforward (z - (C.referenceState, 0)) hzF W hW d c
    hregular.1 hregular.2 hperiod.1 hperiod.2 Θ₁ hΘ₁ θ hdb hcb (n - 1) t ht
  have hi := hbackward (z - (C.referenceState, 0)) hzI W hW d c
    hregular.1 hregular.2 hperiod.1 hperiod.2 Θ₁ hΘ₁ θ hdb hcb t ht n hn
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hpred] at hf
  constructor
  · exact hf.trans (hpack (hBF (n - 1)).le
      ((le_max_left _ _).trans (le_max_right _ _)) (hB n).le hW le_rfl
      (le_max_left flowLoss inverseLoss))
  · exact hi.trans (hpack (hBI n).le
      ((le_max_right _ _).trans (le_max_right _ _)) (hB n).le hW le_rfl
      (le_max_right flowLoss inverseLoss))

end ContinuousFlexibility.Analysis
