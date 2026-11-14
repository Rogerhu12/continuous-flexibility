module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.SpacesTraceRestriction
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Absorbing the fixed material loss in the actual canonical source scale

The output factor H^beta absorbs E0^A and every fixed power of M. Thus the
same global inverse supplied by N05 can be used directly in the low-order
relative estimate, without an auxiliary off-diagonal kernel. All source
elements below are constructed in the selected `VolumeModelData.level`,
and their physical canonical fields are identified by its `forget` formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

/-- The actual material hypotheses absorb one fixed coefficient loss and one fixed inverse loss. -/
theorem n06_material_loss_absorb {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (β A loss : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b,
      T.H r ^ β * T.E0 r ^ A * T.M r ^ loss ≤ C := by
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, hE, hHM, _⟩ := hT
  obtain ⟨CE, hCE, hEbound⟩ := hE A
  obtain ⟨CM, hCM, hMbound, _⟩ := hHM (loss + 1) β hβ
  refine ⟨CE * CM, mul_pos hCE hCM, ?_⟩
  intro r hr
  have hH : 0 < T.H r := (hpos r hr).2.1
  have hM : 0 < T.M r := zero_lt_one.trans_le (hpos r hr).2.2.2
  calc
    T.H r ^ β * T.E0 r ^ A * T.M r ^ loss ≤
        T.H r ^ β * (CE * T.M r) * T.M r ^ loss :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hEbound r hr) (Real.rpow_nonneg hH.le _))
        (Real.rpow_nonneg hM.le _)
    _ = CE * (T.H r ^ β * T.M r ^ (loss + 1)) := by
      rw [Real.rpow_add hM, Real.rpow_one]
      ring
    _ ≤ CE * CM := mul_le_mul_of_nonneg_left (hMbound r hr) hCE.le

section ActualVolume

variable {S : PhysicalSpacesData} {K : CanonicalData S} {V : VolumeModelData S K}
  {T : MaterialData}

private theorem n06_volumeJets_of_sum_bound (s : ℕ)
    (F W : CanonicalVolumeJets S K s)
    (J : ∀ m, PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m))
    {Q : ℝ} (hQ : 0 ≤ Q) (hbound : ∀ m, ‖J m‖ ≤ Q * (‖F m‖ + ‖W m‖)) :
    ∃ Y : CanonicalVolumeJets S K s,
      (∀ m, Y m = J m) ∧ ‖Y‖ ≤ Q * (‖F‖ + ‖W‖) := by
  have hJ : Memℓp J 2 :=
    (((lp.memℓp F).norm.add (lp.memℓp W).norm).const_mul Q).mono hbound
  let Y : CanonicalVolumeJets S K s := ⟨J, hJ⟩
  let major : lp (fun _ : ℕ => ℝ) 2 := Q • (lp.toNorm F + lp.toNorm W)
  have hcoordinate (m : ℕ) : ‖Y m‖ ≤ ‖major m‖ := by
    change ‖J m‖ ≤ ‖Q * (‖F m‖ + ‖W m‖)‖
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hQ (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
    exact hbound m
  have hnorm : ‖Y‖ ≤ ‖major‖ :=
    lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hcoordinate
  refine ⟨Y, fun _ => rfl, hnorm.trans ?_⟩
  calc
    ‖major‖ = Q * ‖lp.toNorm F + lp.toNorm W‖ := by
      simp only [major, norm_smul, Real.norm_eq_abs, abs_of_nonneg hQ]
    _ ≤ Q * (‖lp.toNorm F‖ + ‖lp.toNorm W‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hQ
    _ = Q * (‖F‖ + ‖W‖) := by rw [lp.norm_toNorm, lp.norm_toNorm]

/-- A pointwise square-summable jet estimate constructs an element of the original
canonical source submodule, including its actual weak angular equations. -/
theorem n06Volume_of_piecewise_sum_bound (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s : ℕ) (F W : CanonicalVolumeJets S K s)
    (J : ∀ m, PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m))
    {Q : ℝ} (hQ : 0 ≤ Q) (hbound : ∀ m, ‖J m‖ ≤ Q * (‖F m‖ + ‖W m‖))
    (hreflection : ∀ m, (fun p : PolarPoint => J m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (J m 0 : PolarPoint → ℝ))
    (hweak : ∀ m j, WeakCanonicalAngularDerivative S K m (J m 0) (J m j) j.val) :
    ∃ Y : V.level γ t s,
      (∀ m, Y.val m = J m) ∧
      (∀ m, V.forget γ t s Y m =
        (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • J m 0) ∧
      ‖Y‖ ≤ Q * (‖F‖ + ‖W‖) := by
  obtain ⟨Z, hZ, hnorm⟩ := n06_volumeJets_of_sum_bound s F W J hQ hbound
  have hgraph : Z ∈ canonicalVolumeGraph S K s := by
    constructor
    · intro m
      simpa only [hZ] using hreflection m
    · intro m j
      simpa only [hZ] using hweak m j
  have hmem : Z ∈ V.level γ t s := by
    rw [← SetLike.mem_coe, hV.1 γ t s]
    exact hgraph
  let Y : V.level γ t s := ⟨Z, hmem⟩
  refine ⟨Y, hZ, ?_, hnorm⟩
  intro m
  calc
    V.forget γ t s Y m =
        (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • Y.val m 0 :=
      hV.2.2.2 γ t s Y m
    _ = (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • J m 0 := by
      rw [show Y.val m = J m from hZ m]

/-- Output attenuation removes the fixed material loss before summing over cylinders.
No bound on the multiplicities of `K.cell` is needed. -/
theorem n06Volume_material_absorption {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hV : IsVolumeModel T S K V)
    (β A loss : ℝ) (hβ : 0 < β) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 ≤ θ →
      ∀ F : V.level β 0 s, ∀ W : V.level β (-loss) s,
      ∀ J : ∀ m, PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m),
      (∀ m, ‖J m‖ ≤ θ * T.H (T.sample (K.cell m)) ^ β *
        T.E0 (T.sample (K.cell m)) ^ A *
          (‖F.val m‖ + T.M (T.sample (K.cell m)) ^ loss * ‖W.val m‖)) →
      (∀ m, (fun p : PolarPoint => J m 0 (p.1, Real.pi - p.2))
        =ᵐ[canonicalMeasure S K m] (J m 0 : PolarPoint → ℝ)) →
      (∀ m j, WeakCanonicalAngularDerivative S K m (J m 0) (J m j) j.val) →
      ∃ Y : V.level β 0 s,
        (∀ m, Y.val m = J m) ∧
        (∀ m, V.forget β 0 s Y m = T.H (T.sample (K.cell m)) ^ β • J m 0) ∧
        ‖Y‖ ≤ C * θ * (‖F‖ + ‖W‖) := by
  obtain ⟨C₀, hC₀, hzero⟩ := n06_material_loss_absorb hT β A 0 hβ
  obtain ⟨C₁, hC₁, hloss⟩ := n06_material_loss_absorb hT β A loss hβ
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro θ hθ F W J hlocal hreflection hweak
  have hbound (m : ℕ) : ‖J m‖ ≤ ((C₀ + C₁) * θ) * (‖F.val m‖ + ‖W.val m‖) := by
    have hr := spaces_trace_sample_mem hD hT (K.cell m)
    have h₀ : T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A ≤ C₀ := by
      simpa only [Real.rpow_zero, mul_one] using hzero _ hr
    have h₁ := hloss _ hr
    calc
      ‖J m‖ ≤ θ * T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A *
          (‖F.val m‖ + T.M (T.sample (K.cell m)) ^ loss * ‖W.val m‖) := hlocal m
      _ = θ * ((T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A) * ‖F.val m‖ +
          (T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A *
            T.M (T.sample (K.cell m)) ^ loss) * ‖W.val m‖) := by ring
      _ ≤ θ * (C₀ * ‖F.val m‖ + C₁ * ‖W.val m‖) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _))
            (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))) hθ
      _ ≤ θ * ((C₀ + C₁) * (‖F.val m‖ + ‖W.val m‖)) := by
        apply mul_le_mul_of_nonneg_left _ hθ
        nlinarith only [mul_nonneg hC₀.le (norm_nonneg (W.val m)),
          mul_nonneg hC₁.le (norm_nonneg (F.val m))]
      _ = ((C₀ + C₁) * θ) * (‖F.val m‖ + ‖W.val m‖) := by ring
  obtain ⟨Y, hY, hforget, hnorm⟩ := n06Volume_of_piecewise_sum_bound hV β 0 s
    F.val W.val J (mul_nonneg (add_pos hC₀ hC₁).le hθ) hbound hreflection hweak
  refine ⟨Y, hY, ?_, hnorm⟩
  intro m
  simpa only [neg_zero, Real.rpow_zero, one_mul] using hforget m

/-- This is N05's already selected global inverse, at the fixed base exponent and arbitrary
angular order. Its output occupies precisely the stated material-loss level. -/
theorem n06N05_sameInverse_output_bound {D : ReferenceData}
    {C : NonlinearGeometryData S} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hN05 : N05Properties D T S C K V b B) (s : ℕ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ F : V.level (3 / 4 : ℝ) 0 s,
      ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)).1 m) ∧
        ‖W‖ ≤ C₀ * ‖F‖ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hweighted, _⟩ := hN05
  obtain ⟨C₀, hC₀, hbound⟩ := hweighted 0 s
  refine ⟨C₀, hC₀, ?_⟩
  intro F
  have houtput : ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s,
      V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
        (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)).1 m) ∧
      ‖W‖ + canonicalUnknownScalars S K
        (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)) ≤ C₀ * ‖F‖ := by
    have hF := hbound F
    rw [zero_sub] at hF
    exact hF
  obtain ⟨W, hW, hnorm⟩ := houtput
  have hnonneg : 0 ≤ canonicalUnknownScalars S K
      (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)) := by
    unfold canonicalUnknownScalars
    positivity
  have hWnorm : ‖W‖ ≤ C₀ * ‖F‖ :=
    (le_add_of_nonneg_right hnonneg).trans hnorm
  exact ⟨W, hW, hWnorm⟩

/-- On the fixed graph domain these are exactly the weighted height coordinates of
`B.inverse`, since N05 identifies that map with its same global inverse. -/
theorem n06N05_graphInverse_weighted_output {D : ReferenceData}
    {C : NonlinearGeometryData S} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hN05 : N05Properties D T S C K V b B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ F : V.level (3 / 4 : ℝ) 0 b,
      ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) b,
        (∀ m, (B.inverse F).val.1.1 m =
          (T.M (T.sample (K.cell m)) ^ B.lossMaterial *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) • W.val m 0) ∧
        ‖W‖ ≤ C₀ * ‖F‖ := by
  have hV : IsVolumeModel T S K V := hN05.2.1
  obtain ⟨C₀, hC₀, houtput⟩ := n06N05_sameInverse_output_bound hN05 b
  obtain ⟨_, _, _, _, _, _, _, _, _, hsame, _⟩ := hN05
  refine ⟨C₀, hC₀, ?_⟩
  intro F
  obtain ⟨W, hW, hnorm⟩ := houtput F
  refine ⟨W, ?_, hnorm⟩
  intro m
  rw [hsame F, ← congrFun hW m, hV.2.2.2]
  simp only [neg_neg]

/-- The material estimate and N05's actual global-inverse output give a bound in
the original source norm. The remaining inputs are the local residue's genuine
angular jets and their local estimate; no auxiliary source or inverse is chosen. -/
theorem n06N05_material_absorption {D : ReferenceData}
    {C : NonlinearGeometryData S} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hN05 : N05Properties D T S C K V b B) (A : ℝ) (s : ℕ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ θ : ℝ, 0 ≤ θ →
      ∀ F : V.level (3 / 4 : ℝ) 0 s,
      ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)).1 m) ∧
        ∀ J : ∀ m, PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m),
          (∀ m, ‖J m‖ ≤ θ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (K.cell m)) ^ A *
              (‖F.val m‖ + T.M (T.sample (K.cell m)) ^ B.lossMaterial * ‖W.val m‖)) →
          (∀ m, (fun p : PolarPoint => J m 0 (p.1, Real.pi - p.2))
            =ᵐ[canonicalMeasure S K m] (J m 0 : PolarPoint → ℝ)) →
          (∀ m j, WeakCanonicalAngularDerivative S K m (J m 0) (J m j) j.val) →
          ∃ Y : V.level (3 / 4 : ℝ) 0 s,
            (∀ m, Y.val m = J m) ∧
            (∀ m, V.forget (3 / 4 : ℝ) 0 s Y m =
              T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) • J m 0) ∧
            ‖Y‖ ≤ C₀ * θ * ‖F‖ := by
  have hV : IsVolumeModel T S K V := hN05.2.1
  obtain ⟨Cinv, hCinv, houtput⟩ := n06N05_sameInverse_output_bound hN05 s
  obtain ⟨Cmat, hCmat, habsorb⟩ :=
    n06Volume_material_absorption hD hT hV (3 / 4 : ℝ) A B.lossMaterial
      (by norm_num) s
  refine ⟨Cmat * (1 + Cinv), mul_pos hCmat (by positivity), ?_⟩
  intro θ hθ F
  obtain ⟨W, hW, hnorm⟩ := houtput F
  refine ⟨W, hW, ?_⟩
  intro J hlocal hreflection hweak
  obtain ⟨Y, hY, hforget, hYnorm⟩ :=
    habsorb θ hθ F W J hlocal hreflection hweak
  refine ⟨Y, hY, hforget, hYnorm.trans ?_⟩
  calc
    Cmat * θ * (‖F‖ + ‖W‖) ≤ Cmat * θ * (‖F‖ + Cinv * ‖F‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hnorm) (mul_nonneg hCmat.le hθ)
    _ = (Cmat * (1 + Cinv)) * θ * ‖F‖ := by ring

end ActualVolume

end ContinuousFlexibility.Statements
