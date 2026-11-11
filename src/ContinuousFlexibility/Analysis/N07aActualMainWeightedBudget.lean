import ContinuousFlexibility.Analysis.N07aActualMainModeBound
import ContinuousFlexibility.Analysis.N07aRelativeMainReflection
import ContinuousFlexibility.Analysis.N07aReferenceEnergyBudget
import ContinuousFlexibility.Analysis.N07aScalarColumnVolumes
import ContinuousFlexibility.Analysis.N07aAngularBlockWeights

/-!
# The actual relative main blocks in the prescribed outer weighted norm

The complete geometric envelope is absorbed once after the fixed-order
reference energy majorant has been inserted.  The resulting true lp
majorant retains the angular gap decay and one parameter seminorm, with
one loss independent of both output orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ENNReal

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aMainWeightedBudgetLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aMainWeightedBudgetLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aMainWeightedBudgetUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aMainWeightedBudgetUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aMainWeightedBudgetGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aMainWeightedBudgetGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private theorem n07a_mainWeightedBand_unitMode {m : ℕ} (hm : K.left m < K.right m)
    (f : CanonicalL2 S K m) (hf : n07aAngularReflection m f = f)
    (l : ℕ) (a κ : ℝ) (ha : 0 ≤ a) :
    a * ‖n07aAngularBand m hm l (κ • f)‖ =
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ‖(a * κ) • n07aCanonicalUnitMode hm f l‖ := by
  rw [map_smul, norm_smul, n07aAngularBand_norm_unitMode hm f hf l,
    norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
  ring

private theorem n07a_mainWeightedMajorant_factor (A n A₀ x : ℝ) :
    (A * n) * (A₀ * x) = (A * A₀) * n * x := by
  ring

private theorem n07a_mainWeightedGap_le
    (J v H τ e n E e₀ w a₀ A g x : ℝ)
    (hJ : 0 ≤ J) (hv : 0 ≤ v) (hH : 0 ≤ H) (hτ : 0 ≤ τ)
    (he : 0 ≤ e) (hn : 0 ≤ n) (ha₀ : 0 ≤ a₀)
    (hb : g * x ≤ H * τ * (e * n) * E)
    (hp : J * E ≤ e₀ * w * a₀)
    (hew : v * H * w * (e * e₀) ≤ A) :
    J * (v * g * x) ≤ τ * (A * n * a₀) := by
  calc
    _ ≤ J * (v * (H * τ * (e * n) * E)) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hv) hJ
    _ = (v * H * τ * e * n) * (J * E) := by ring
    _ ≤ (v * H * τ * e * n) * (e₀ * w * a₀) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (v * H * w * (e * e₀)) * (τ * n * a₀) := by ring
    _ ≤ A * (τ * n * a₀) :=
      mul_le_mul_of_nonneg_right hew (mul_nonneg (mul_nonneg hτ hn) ha₀)
    _ = _ := by ring

theorem n07a_actualRelativeMain_weighted_gap_budget
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hI : ∀ m, K.left m < K.right m) :
    ∃ d : ℕ, ∀ t : ℝ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∀ j (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
      ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧
        ‖a‖ ≤ A * parameterGrading S (s + d) z * ‖F‖ ∧
        ∀ l (commute : Bool) m,
          Real.sqrt (n07aAngularJetWeightSq b j) *
            ((n07aVolumeWeight T K (3 / 4 : ℝ) t m)⁻¹ * n07aAngularGap j l ^ s *
              ‖n07aAngularBand m (hI m) l
                ((if commute then ((l : ℝ) - j) else 1) •
                  n07aRelativeMainSource (P := P) href hcur z hz F m (hI m))‖) ≤
            n07aAngularTail ((j : ℤ) - l) * a m := by
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  let columns := n07a_referenceScalarColumns_volume hD hS hT h01 h03 h04
    href h05.2.1 (3 / 4 : ℝ) (0 - B.lossMaterial) 0
  let Col : Fin 3 → V.level (3 / 4 : ℝ) (0 - B.lossMaterial) 0 := columns.choose
  have hCol := columns.choose_spec
  let energy := n07a_referenceEnergy_outer_budget hD hT href h05 hI Col hCol
  let A₀ : ℝ := energy.choose
  have hA₀ : 0 < A₀ := energy.choose_spec.1
  let e₀ : ℕ → ℝ := energy.choose_spec.2.choose
  have he₀ : N07aSampleSubpower T K e₀ := energy.choose_spec.2.choose_spec.1
  have he₀1 : ∀ m, 1 ≤ e₀ m := energy.choose_spec.2.choose_spec.2.1
  have henergy := energy.choose_spec.2.choose_spec.2.2
  let modes := n07a_actualRelativeMain_mode_bound hD hS hT h01 h02 h03 h04
    href hcur hprincipal h05 h06 hI
  let d₁ : ℕ := modes.choose
  let d₂ : ℕ := modes.choose_spec.choose
  have hmode := modes.choose_spec.choose_spec
  let d : ℕ := 4 + max d₁ d₂
  refine ⟨d, fun t s => ?_⟩
  let modeBounds := hmode s
  let e₁ : ℕ → ℝ := modeBounds.choose
  let e₂ : ℕ → ℝ := modeBounds.choose_spec.choose
  have he₁ : N07aSampleSubpower T K e₁ := modeBounds.choose_spec.choose_spec.1
  have he₂ : N07aSampleSubpower T K e₂ := modeBounds.choose_spec.choose_spec.2.1
  have he₁0 : ∀ m, 0 ≤ e₁ m := modeBounds.choose_spec.choose_spec.2.2.1
  have he₂0 : ∀ m, 0 ≤ e₂ m := modeBounds.choose_spec.choose_spec.2.2.2.1
  have hmodes := modeBounds.choose_spec.choose_spec.2.2.2.2
  let e : ℕ → ℝ := fun m => e₁ m + e₂ m
  have he : N07aSampleSubpower T K e := he₁.add he₂
  have he0 (m : ℕ) : 0 ≤ e m := add_nonneg (he₁0 m) (he₂0 m)
  have he₀0 (m : ℕ) : 0 ≤ e₀ m := zero_le_one.trans (he₀1 m)
  have hprod : N07aSampleSubpower T K (fun m => e m * e₀ m) :=
    N07aSampleSubpower.mul hD hT he he₀
  let absorption := hprod.volume_gain_absorption hD hT
    (by norm_num : (0 : ℝ) < 3 / 4) t (0 - B.lossMaterial)
  let A : ℝ := absorption.choose
  have hA : 0 < A := absorption.choose_spec.1
  have hweight := absorption.choose_spec.2
  refine ⟨A * A₀, mul_pos hA hA₀, fun z hz j F hF hU => ?_⟩
  let majorant := henergy j F hF hU
  let a₀ : lp (fun _ : ℕ => ℝ) 2 := majorant.choose
  have ha₀ : ∀ m, 0 ≤ a₀ m := majorant.choose_spec.1
  have hnorm : ‖a₀‖ ≤ A₀ * ‖F‖ := majorant.choose_spec.2.1
  have hpieces := majorant.choose_spec.2.2
  let n : ℝ := parameterGrading S (s + d) z
  have hn : 0 ≤ n := apply_nonneg _ _
  let a : lp (fun _ : ℕ => ℝ) 2 := (A * n) • a₀
  have ha (m : ℕ) : a m = A * n * a₀ m := by
    simp only [a, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  refine ⟨a, fun m => by rw [ha]; exact mul_nonneg (mul_nonneg hA.le hn) (ha₀ m), ?_, ?_⟩
  · dsimp only [a]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA.le hn)]
    exact (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hA.le hn)).trans_eq
      (n07a_mainWeightedMajorant_factor A n A₀ ‖F‖)
  · intro l commute m
    let f := n07aRelativeMainSource (P := P) href hcur z hz F m (hI m)
    let κ : ℝ := if commute then ((l : ℝ) - j) else 1
    let H : ℝ := T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)
    let v : ℝ := (n07aVolumeWeight T K (3 / 4 : ℝ) t m)⁻¹
    let w : ℝ := n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m
    let J : ℝ := Real.sqrt (n07aAngularJetWeightSq b j)
    let τ : ℝ := n07aAngularTail ((j : ℤ) - l)
    let E : ℝ := ‖n07aReferenceInverseField (B := B) F m‖ +
      ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
        (V.forget (3 / 4 : ℝ) 0 b F)‖
    have hH : 0 ≤ H := (Real.rpow_pos_of_pos
      (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.1 _).le
    have hv : 0 ≤ v := (inv_pos.mpr (n07aVolumeWeight_pos hD hT _ _ m)).le
    have hJ : 0 ≤ J := Real.sqrt_nonneg _
    have hτ : 0 ≤ τ := by unfold τ n07aAngularTail; positivity
    have hem : 0 ≤ e m := he0 m
    have hE : 0 ≤ E := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hband : n07aAngularBand m (hI m) j (n07aReferenceInverseField (B := B) F m) =
        n07aReferenceInverseField (B := B) F m := by
      simpa only [n07aAngularUnknownBand_field, n07aReferenceInverseField] using
        congrArg (fun u : CanonicalUnknown S K => u.1 m) hU
    have hf : n07aAngularReflection m f = f :=
      n07aRelativeMainSource_reflection hS h01 h03 h04 href hcur h05.2.1 z hz F m (hI m)
    have hn₁ : parameterGrading S (s + 4 + d₁) z ≤ n :=
      hmono (show s + 4 + d₁ ≤ s + d by dsimp only [d]; omega) z
    have hn₂ : parameterGrading S (s + 4 + d₂) z ≤ n :=
      hmono (show s + 4 + d₂ ≤ s + d by dsimp only [d]; omega) z
    have hc : e₁ m * parameterGrading S (s + 4 + d₁) z +
        e₂ m * parameterGrading S (s + 4 + d₂) z ≤ e m * n :=
      (add_le_add (mul_le_mul_of_nonneg_left hn₁ (he₁0 m))
        (mul_le_mul_of_nonneg_left hn₂ (he₂0 m))).trans_eq
          (add_mul (e₁ m) (e₂ m) n).symm
    have hraw := (hmodes z hz F m j l hband commute).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (mul_nonneg hH hτ)) hE)
    have hmodeeq : n07aAngularGap j l ^ s * ‖n07aAngularBand m (hI m) l (κ • f)‖ =
        Real.sqrt (Real.pi * (K.right m - K.left m)) *
          ‖(n07aAngularGap j l ^ s * κ) • n07aCanonicalUnitMode (hI m) f l‖ := by
      exact n07a_mainWeightedBand_unitMode (hI m) f hf l (n07aAngularGap j l ^ s) κ
        (pow_nonneg (zero_le_one.trans (n07aAngularGap_one_le j l)) s)
    have hb : n07aAngularGap j l ^ s * ‖n07aAngularBand m (hI m) l (κ • f)‖ ≤
        H * τ * (e m * n) * E := by
      have hgap := congrArg (fun q : ℝ =>
        Real.sqrt (Real.pi * (K.right m - K.left m)) *
          ‖(q ^ s * κ) • n07aCanonicalUnitMode (hI m) f l‖)
        (n07aAngularGap_eq_int j l)
      exact (hmodeeq.trans hgap).le.trans hraw
    have hew : v * H * w * (e m * e₀ m) ≤ A := by
      have h := hweight m
      rw [abs_of_nonneg (mul_nonneg (he0 m) (he₀0 m))] at h
      exact h
    have hp := hpieces m
    change J * E ≤ e₀ m * w * a₀ m at hp
    have hfinal := n07a_mainWeightedGap_le J v H τ (e m) n E (e₀ m) w (a₀ m) A
      (n07aAngularGap j l ^ s) ‖n07aAngularBand m (hI m) l (κ • f)‖
      hJ hv hH hτ hem hn (ha₀ m) hb hp hew
    exact hfinal.trans_eq (congrArg (τ * ·) (ha m).symm)

end ContinuousFlexibility.Analysis
