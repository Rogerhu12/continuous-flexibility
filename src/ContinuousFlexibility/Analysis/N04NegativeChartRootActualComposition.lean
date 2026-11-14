module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootComposition
public import ContinuousFlexibility.Analysis.N04NegativeChartRootRepresentative
public import ContinuousFlexibility.Analysis.N04NegativeChartRootLowInput
public import ContinuousFlexibility.Analysis.N04NegativeChartRootScale

/-! The complete root displacement on the original sector plot.
The low base and the actual material scale precede every state order.
The field and label prefixes are aligned without replacing their
per-state degree by the largest state order. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem rootComposition_fraction {R : ℝ} (hR : 0 ≤ R) (a b : ℕ) :
    R ^ ((a : ℝ) / ((b : ℝ) + 1)) =
      (R ^ ((1 : ℝ) / ((b : ℝ) + 1))) ^ a := by
  rw [← Real.rpow_mul_natCast hR ((1 : ℝ) / ((b : ℝ) + 1)) a]
  congr 1
  ring

namespace N04RealizationStart.NegativeOpticalFactors

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

set_option backward.isDefEq.respectTransparency true

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : W.NegativeOpticalFactors e} {base loss : ℕ}

/-- This is the coefficient already selected by the actual low-input
theorem, so its scale and its low-order bounds use exactly one choice. -/
def FullHalfFieldPowerControl.rootCompositionScaleCoefficient
    (Q : F.FullHalfFieldPowerControl base loss) : ℝ :=
  Q.root_low_input.choose_spec.choose_spec.choose

theorem FullHalfFieldPowerControl.actualRootComposition_prefix
    (Q : F.FullHalfFieldPowerControl base loss) :
    ∃ b : ℕ, ∃ ε : ℝ,
      W.base ≤ b ∧ base ≤ b ∧ Q.root_low_input.choose ≤ b ∧
      0 < ε ∧ ε ≤ min (W.ε / 2) (1 / 2 : ℝ) ∧ ε ≤ Q.root_low_input.choose_spec.choose ∧
      1 ≤ Q.rootCompositionScaleCoefficient ∧
      ∀ N : ℕ, 0 < N → ∃ D : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m side (δ : ℝ), 0 < δ →
        δ ≤ W.negativeChartRootScale e Q.rootCompositionScaleCoefficient m side →
      ∀ z ∈ sectorNeighborhood W.S b ε ε, parameterGrading W.S b z ≤ 1 →
      ∀ L : (Fin 1 → ℝ) →L[ℝ] Parameter W.S,
      ∀ A : NegativeRootRepresentative F b ε z L m side δ,
      ∀ k, k ≤ N → ∀ v : Fin k → (Fin 1 → ℝ),
        (∀ a, parameterGrading W.S b (L (v a)) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (b + s + D * N + 1) z ≤ R →
        (∀ a, parameterGrading W.S (b + s + D * N + 1) (L (v a)) ≤ R) →
      ∀ j, j ≤ s + 1 → ∀ q : N04FlowPoint,
        q.1 ∈ n04FlowParameterBox → 0 < q.1.1 →
        ‖iteratedFDeriv ℝ j (fun q : N04FlowPoint =>
          iteratedFDeriv ℝ k (fun y => A.h (y, A.flow.inverse y q.1 1 q.2) - q.2) 0 v) q‖ ≤
          B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
            parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
            R ^ (((j - 1 + D * k : ℕ) : ℝ) / (((s + D * N : ℕ) : ℝ) + 1)) := by
  have hlow := Q.root_low_input
  let b₀ := hlow.choose
  let ε₀ := hlow.choose_spec.choose
  have hl := hlow.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hC : 1 ≤ Q.rootCompositionScaleCoefficient := hl.2.2.2.2.1
  have hf := Q.actualRootField_prefix (P := Fin 1 → ℝ)
  have hh := W.negativeRootLabel_field_prefix e
  let bf := hf.choose
  let bh := hh.choose
  let b := max b₀ (max bf bh)
  let ε := min ε₀ W.negativeHalfStateRadius
  have hb₀ : b₀ ≤ b := le_max_left _ _
  have hbf : bf ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hbh : bh ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  have hbW : W.base ≤ b := hl.1.trans hb₀
  have hbbase : base ≤ b := hf.choose_spec.1.trans hbf
  have hε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεhalf : ε ≤ W.negativeHalfStateRadius := min_le_right _ _
  have hεW : ε ≤ W.ε / 2 := hεhalf.trans (min_le_left _ _)
  have hεold : ε ≤ W.ε := hεW.trans (by linarith only [W.ε_pos])
  have hε : 0 < ε := lt_min hl.2.2.1
    (lt_min (by linarith only [W.ε_pos]) (by norm_num))
  refine ⟨b, ε, hbW, hbbase, hb₀, hε, hεhalf, hε₀, hC, fun N hN => ?_⟩
  have hfs := hf.choose_spec.2 N
  have hhs := hh.choose_spec.2 N
  let df := hfs.choose
  let dh := hhs.choose
  let shift := max df dh
  have hheight := materialSample_H_M_envelope W.hT W.radial.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH := max 1 hheight.choose
  have hRH : 1 ≤ RH := le_max_left _ _
  have hcomp := n04NegativeChart_rootComposition_prefix (P := Fin 1 → ℝ) N shift RH hRH
  let D := hcomp.choose
  have hD := hcomp.choose_spec.1
  have hdf : df ≤ shift := le_max_left _ _
  have hdh : dh ≤ shift := le_max_right _ _
  refine ⟨D, fun s => ?_⟩
  let sf := s + (D - df) * N
  let sh := s + (D - dh) * N
  have hdfD : df ≤ D := hdf.trans (by omega)
  have hdhD : dh ≤ D := hdh.trans (by omega)
  have hsf : sf + df * N = s + D * N := by
    dsimp only [sf]; rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hdfD]
  have hsh : sh + dh * N = s + D * N := by
    dsimp only [sh]; rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hdhD]
  have hpad (d : ℕ) (hd : d ≤ shift) : s + 1 + N + 1 ≤ s + (D - d) * N + 1 := by
    have ht : 3 * N ≤ (D - d) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hfb := hfs.choose_spec sf
  have hhb := hhs.choose_spec sh
  let Cf := hfb.choose
  let Ch := hhb.choose
  let C := max 1 (max Cf Ch)
  have hCf : Cf ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCh : Ch ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hCone : 1 ≤ C := le_max_left _ _
  have hcb := hcomp.choose_spec.2 (s + 1)
  let Cg := hcb.choose
  let eg := hcb.choose_spec.choose
  have hCg := hcb.choose_spec.choose_spec.1
  have henv := coefficientEnvelope_pack (Cg * C ^ eg) (C * (eg : ℝ))
  let B := henv.choose
  refine ⟨B, henv.choose_spec.1, ?_⟩
  intro m side δ hδ hδscale z hz hzlow L A k hk v hv₀ R hR hzR hv₁ j hj q hq hqx
  let x := liftSectorParameter W.S W.C z
  let Lx := (sectorParameterInclusion W.S).comp L
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let M := C * E ^ C
  let ρ := R ^ ((1 : ℝ) / (((s + D * N : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hHR : H ≤ RH := (show H ≤ hheight.choose from by
    simpa only [H, Real.rpow_zero, mul_one] using hheight.choose_spec.2
      ((W.A e).cell (e.symm (.inl (m, side))))).trans (le_max_right _ _)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hCone
    (Real.one_le_rpow hE (zero_le_one.trans hCone))
  have hρ : 1 ≤ ρ := Real.one_le_rpow hR (by positivity)
  have ha (y : Fin 1 → ℝ) : liftSectorParameter W.S W.C (z + L y) = x + Lx y := by
    simp only [x, Lx, liftSectorParameter_eq_affine, map_add,
      ContinuousLinearMap.comp_apply, add_assoc]
  have hstate (n : ℕ) : pairGrading (stateGrading W.S) realGrading n
      (x - (W.C.referenceState, 0)) = parameterGrading W.S n z := by
    simpa only [x, liftSectorParameter_sub_reference, pairGrading_sectorParameterInclusion, parameterGrading]
  have hdir (n : ℕ) (y : Fin 1 → ℝ) : pairGrading (stateGrading W.S) realGrading n
      (Lx y) = parameterGrading W.S n (L y) := rfl
  have hx := liftSectorParameter_mem_stateNeighborhood (C := W.C)
    (sectorNeighborhood_mono W.S hbbase hεhalf hεhalf hz) le_rfl
  have hx₀ := liftSectorParameter_mem_stateNeighborhood (C := W.C)
    (sectorNeighborhood_mono W.S hb₀ hε₀ hε₀ hz) le_rfl
  have hzw := sectorNeighborhood_mono W.S hbW hεold hεold hz
  have hfields : ∀ y ∈ A.V, ∀ p ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ,
      A.d (y, p) = F.fullHalfDrift (x + Lx y) m side p ∧
      A.c (y, p) = F.fullHalfSpeed (x + Lx y) m side p := by
    intro y hy p hp
    simpa only [ha y] using A.fields y hy p ⟨hp.1.1.le, hp.1.2.le⟩
  have hs := W.negativeChartRootScale_bounds e hC m side
  have hδone : δ ≤ 1 := hδscale.trans hs.2.1
  have hδwidth : δ < W.negativeOpticalWidth m side := by
    have hh := (W.negativeMaterialCollar_bounds m).2.2.2 side
    linarith only [hs.2.2.1, hh, hδscale, hδ]
  have hsmall : 4 * δ * (Q.rootCompositionScaleCoefficient * E ^ Q.rootCompositionScaleCoefficient) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδscale (by norm_num : (0 : ℝ) ≤ 4))
      (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_le_one.trans hE) _))).trans
        hs.2.2.2.2
  have hangle := (hl.2.2.2.2.2.2.2 x hx₀
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m side δ hδ hδone hδwidth.le hsmall
    1 A.d A.c A.hd A.hc A.dp A.cp A.flow 0
    (fun p hp => by simpa only [L.map_zero, add_zero, x] using A.fields 0 A.zero_V p hp)).1
  let p₀ := (parameterGrading W.S b).comp L.toLinearMap
  let p₁ := (parameterGrading W.S (b + s + D * N + 1)).comp L.toLinearMap
  have hbudget (a : ℝ) (haC : a ≤ C) (d : ℕ) (hd : d ≤ shift) (l r : ℕ) :
      a * E ^ a * parameterHeightWeight H r *
        R ^ (((l - 1 + d * r : ℕ) : ℝ) / (((s + D * N : ℕ) : ℝ) + 1)) ≤
          M * parameterHeightWeight H r * ρ ^ (l - 1 + shift * r) := by
    rw [rootComposition_fraction (zero_le_one.trans hR)]
    have hm : a * E ^ a ≤ M := mul_le_mul haC
      (Real.rpow_le_rpow_of_exponent_le hE haC)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hCone)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hm (parameterHeightWeight_nonneg hH r))
      (pow_le_pow_right₀ hρ (Nat.add_le_add_left (Nat.mul_le_mul_right r hd) _))
      (pow_nonneg (zero_le_one.trans hρ) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH r))
  have hraw : ∀ r, r ≤ N → ∀ u : Fin r → (Fin 1 → ℝ),
      (∀ a, p₀ (u a) ≤ 1) → (∀ a, p₁ (u a) ≤ R) → ∀ l, l ≤ s + 1 + N + 1 →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
      ‖iteratedFDeriv ℝ l (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootPlotField A.d A.c δ) r (0, y.1)
          (fun a => (u a, (0 : PolarPoint))) (t, y.2)) (q.1, θ)‖ ≤
          M * parameterHeightWeight H r * ρ ^ (l - 1 + shift * r) := by
    intro r hr u hu₀ hu₁ l hl t ht θ
    have hgl : pairGrading (stateGrading W.S) realGrading bf (x - (W.C.referenceState, 0)) ≤ 1 := by
      rw [hstate]; exact (sectorPairGrading_monotone W.S hbf z).trans hzlow
    have high : bf + sf + df * N + 1 ≤ b + s + D * N + 1 := by omega
    have hgz : pairGrading (stateGrading W.S) realGrading (bf + sf + df * N + 1)
        (x - (W.C.referenceState, 0)) ≤ R := by
      rw [hstate]; exact (sectorPairGrading_monotone W.S high z).trans hzR
    have hb := hfb.choose_spec.2 m side r hr l (hl.trans (hpad df hdf)) x hx hgl
      Lx A.d A.c A.hd A.hc A.V A.open_V A.zero_V hfields u
      (fun a => by rw [hdir]; exact (sectorPairGrading_monotone W.S hbf (L (u a))).trans (hu₀ a))
      R hR hgz
      (fun a => by rw [hdir]; exact (sectorPairGrading_monotone W.S high (L (u a))).trans (hu₁ a))
      δ hδ hδone hδwidth (q.1, θ) hq hqx t ht
    exact hb.trans (by
      simpa only [← hsf] using hbudget Cf hCf df hdf l r)
  have hlabel : ∀ r, r ≤ N → ∀ u : Fin r → (Fin 1 → ℝ),
      (∀ a, p₀ (u a) ≤ 1) → (∀ a, p₁ (u a) ≤ R) → ∀ l, l ≤ s + 1 + N + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ l (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootLabelField A.h) r (0, y.1)
          (fun a => (u a, (0 : PolarPoint))) (1, y.2)) (q.1, θ)‖ ≤
          M * parameterHeightWeight H r * ρ ^ (l - 1 + shift * r) := by
    intro r hr u hu₀ hu₁ l hl θ
    have high : bh + sh + dh * N + 1 ≤ b + s + D * N + 1 := by omega
    have hb := hhb.choose_spec.2 (Fin 1 → ℝ) r hr l (hl.trans (hpad dh hdh)) m side z hzw
      ((sectorPairGrading_monotone W.S hbh z).trans hzlow) L A.h A.hh A.V A.open_V A.zero_V A.label u
      (fun a => (sectorPairGrading_monotone W.S hbh (L (u a))).trans (hu₀ a)) R hR
      ((sectorPairGrading_monotone W.S high z).trans hzR)
      (fun a => (sectorPairGrading_monotone W.S high (L (u a))).trans (hu₁ a)) 1 (q.1, θ)
    exact hb.trans (by
      simpa only [← hsh] using hbudget Ch hCh dh hdh l r)
  let I : NegativeChartRootCompositionInput (Fin 1 → ℝ) N (s + 1) shift RH := {
    d := A.d, c := A.c, hd := A.hd, hc := A.hc, dp := A.dp, cp := A.cp,
    δ := δ, flow := A.flow, q := q, p₀ := p₀, p₁ := p₁, R := R, H := H, M := M, ρ := ρ,
    hR := hR, hH := hH, hHR := hHR, hM := hM, hρ := hρ,
    angle := fun t ht θ => hangle (q.1, θ) hq hqx.le t ht,
    raw := hraw, h := A.h, hh := A.hh, label_raw := hlabel }
  have hb := hcb.choose_spec.choose_spec.2 I k hk v hv₀ hv₁ j hj
  have hm : Cg * M ^ eg ≤ B * E ^ B := by
    calc
      _ = (Cg * C ^ eg) * E ^ (C * (eg : ℝ)) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE) C eg]
        ring
      _ ≤ _ := henv.choose_spec.2 E hE
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm (parameterHeightWeight_nonneg hH k))
    (pow_nonneg (zero_le_one.trans hρ) (j - 1 + D * k))
  have hb' := hb.trans hp
  exact hb'.trans_eq (congrArg (fun t : ℝ => B * E ^ B * parameterHeightWeight H k * t)
    (rootComposition_fraction (zero_le_one.trans hR) (j - 1 + D * k) (s + D * N)).symm)

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.actualRootComposition_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.actualRootComposition_prefix
