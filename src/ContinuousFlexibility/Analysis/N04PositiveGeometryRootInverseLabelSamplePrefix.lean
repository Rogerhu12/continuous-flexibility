import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseLabelPositiveWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelPrefix

/-!
# A common sampled prefix for the inverse label and its slope

The low base is fixed before the parameter prefix. Reindexing each
angular horizon aligns both the high seminorm and the denominator of
the normalized power. Only positive words of the angular lift are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04RootInverseLabelSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootInverseLabel_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ Jα : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2),
      ∀ Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          deriv (Function.invFun
            (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side))) y.2),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      let P := fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
        pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R
      let M := A * W.U.E0 (W.U.sample (X.cell i)) ^ A
      let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
      let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
      N04BoundaryPositiveWordBounds Jα K s 1 z θ P M H t shift ∧
        N04BoundaryWordBounds Jb K s 1 z θ P M H t shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  obtain ⟨Bd, hBd, pd⟩ :=
    n04PositiveGeometry_rootInverseDefect_fixedBase_prefix_of_flow W.hT W.hS hN hflow
  obtain ⟨Bb, hBb, pb⟩ :=
    n04PositiveGeometry_rootInverseDerivative_fixedBase_prefix_of_flow W.hT W.hS hN hflow
  let low := Bd + Bb
  have hdl : Bd ≤ low := by dsimp only [low]; omega
  have hbl : Bb ≤ low := by dsimp only [low]; omega
  refine ⟨low, hBd.trans hdl, fun K => ?_⟩
  obtain ⟨cd, pdc⟩ := pd K
  obtain ⟨cb, pbc⟩ := pb K
  let shift := cd + cb
  have hcd : cd ≤ shift := by dsimp only [shift]; omega
  have hcb : cb ≤ shift := by dsimp only [shift]; omega
  refine ⟨shift, fun s => ?_⟩
  let sd := s + (shift - cd) * K
  let sb := s + (shift - cb) * K
  obtain ⟨Ad, hAd, hd⟩ := pdc sd
  obtain ⟨Ab, hAb, hb'⟩ := pbc sb
  obtain ⟨Cd, hCd, htd⟩ := n04PositiveGeometry_positiveSource_circle_parameter_weight
    W X (3 / 4 : ℝ) (A := 0) (C := Ad) (by norm_num) (zero_le_one.trans hAd)
  obtain ⟨Cb, hCb, htb⟩ := n04PositiveGeometry_positiveSource_circle_parameter_weight
    W X (3 / 4 : ℝ) (A := 0) (C := Ab) (by norm_num) (zero_le_one.trans hAb)
  let A := Cd + Cb + 1
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  have hCdA : Cd ≤ A := by dsimp only [A]; linarith
  have hCbA : Cb ≤ A := by dsimp only [A]; linarith
  refine ⟨A, hA, ?_⟩
  intro i side m hm Jα Jb z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := A * E ^ A
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans hA)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {B : ℝ} (hBA : B ≤ A) : B * E ^ B ≤ M :=
    mul_le_mul hBA (Real.rpow_le_rpow_of_exponent_le hE hBA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hden (c : ℕ) (hc : c ≤ shift) :
      (s + (shift - c) * K) + c * K = s + shift * K := by
    calc
      _ = s + ((shift - c) + c) * K := by ring
      _ = _ := by rw [Nat.sub_add_cancel hc]
  have hhigh (l c : ℕ) (hl : l ≤ low) (hc : c ≤ shift) :
      l + (s + (shift - c) * K) + c * K + 1 ≤ low + s + shift * K + 1 := by
    have he := hden c hc
    omega
  have htpow (a : ℕ) : t ^ a =
      R ^ ((a : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  have hfinish {c u k : ℕ} {Z v : ℝ} (hc : c ≤ shift)
      (hZ : Z ≤ M * parameterHeightWeight H k)
      (hv : ‖v‖ ≤ Z * R ^ (((u + c * k : ℕ) : ℝ) /
        ((((s + (shift - c) * K) + c * K : ℕ) : ℝ) + 1))) :
      ‖v‖ ≤ M * parameterHeightWeight H k * t ^ (u + shift * k) := by
    have hpow : R ^ (((u + c * k : ℕ) : ℝ) /
        ((((s + (shift - c) * K) + c * K : ℕ) : ℝ) + 1)) ≤
        t ^ (u + shift * k) := by
      rw [hden c hc, ← htpow (u + c * k)]
      exact pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right k hc) u)
    exact hv.trans (mul_le_mul hZ hpow (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (mul_nonneg hM (parameterHeightWeight_nonneg hH k)))
  have hmatb (k : ℕ) : Ab * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
      M * parameterHeightWeight H k := by
    have h := htb i side m hm k
    have h' : Ab * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
        Cb * E ^ Cb * parameterHeightWeight H k := by
      simpa only [Real.rpow_zero, mul_one] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (hcost hCbA) (parameterHeightWeight_nonneg hH k))
  have hmatd (k : ℕ) (hk : 0 < k) : Ad * (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) ≤
      M * parameterHeightWeight H k := by
    have h := htd i side m hm k
    have h' : Ad * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
        Cd * E ^ Cd * parameterHeightWeight H k := by
      simpa only [Real.rpow_zero, mul_one] using h
    have h'' := h'.trans
      (mul_le_mul_of_nonneg_right (hcost hCdA) (parameterHeightWeight_nonneg hH k))
    simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hk)] using h''
  have hslope (k : ℕ) (hk : k ≤ K) (u : ℕ) (hu : u ≤ s) (d : ℕ) (hd' : d ≤ 1)
      (J : SmoothDirections (sectorNeighborhood W.S base ε ε) (fun x =>
        iteratedDeriv (u + d) (deriv (Function.invFun
          (n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m (!side)))) θ))
      (v : Fin k → (StateDirections W.S × ℝ)) (hv : ∀ j, P (v j)) :
      ‖J.D k z v‖ ≤ M * parameterHeightWeight H k * t ^ (u + shift * k) := by
    have h := hb' k hk d (by omega) u (by dsimp only [sb]; omega) (!side) m θ J z hz
      ((hp hbl z).trans hzlow) v (fun j => (hp hbl (v j)).trans (hv j).1) R hR
      ((hp (hhigh Bb cb hbl hcb) z).trans hzR)
      (fun j => (hp (hhigh Bb cb hbl hcb) (v j)).trans (hv j).2)
    exact hfinish hcb (hmatb k) (by simpa only [Real.norm_eq_abs] using h)
  let Jδ : SmoothDirections (sectorNeighborhood W.S base ε ε) (fun x =>
      Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m (!side)) θ - θ) :=
    n04PositiveGeometry_rootInverseDefect_angularDirections W.hT W.hS hN (!side) m 0 θ
  have hdefect (k : ℕ) (hkpos : 0 < k) (hk : k ≤ K)
      (v : Fin k → (StateDirections W.S × ℝ)) (hv : ∀ j, P (v j)) :
      ‖Jδ.D k z v‖ ≤ M * parameterHeightWeight H k * t ^ (shift * k) := by
    have h := hd k hk 0 (Nat.zero_le _) 0 (by omega) (!side) m θ Jδ z hz
      ((hp hdl z).trans hzlow) v (fun j => (hp hdl (v j)).trans (hv j).1) R hR
      ((hp (hhigh Bd cd hdl hcd) z).trans hzR)
      (fun j => (hp (hhigh Bd cd hdl hcd) (v j)).trans (hv j).2)
    simpa only [Nat.zero_add] using
      hfinish (u := 0) hcd (hmatd k hkpos) (by simpa only [Real.norm_eq_abs] using h)
  constructor
  · exact n04PositiveGeometry_inverseLabel_positive_words Jα Jb K s z hz θ P Jδ M H t shift hdefect
      (fun k hk u hu v hv => by
        simpa only [Nat.add_zero] using hslope k hk u hu 0 (by omega)
          (smoothDirections_angularStateSlice Jb (u + 0) θ) v hv)
  · apply n04PositiveGeometry_boundaryWord_of_angular Jb
      (smoothDirections_angularStateSlice Jb) K s 1 z hz θ P M H t shift
    intro k hk u hu d hd' v hv
    exact hslope k hk u hu d hd' (smoothDirections_angularStateSlice Jb (u + d) θ) v hv

end ContinuousFlexibility.Analysis
