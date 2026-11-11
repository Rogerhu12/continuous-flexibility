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
  obtain ⟨Col, hCol⟩ := n07a_referenceScalarColumns_volume hD hS hT h01 h03 h04
    href h05.2.1 (3 / 4 : ℝ) (0 - B.lossMaterial) 0
  obtain ⟨A₀, hA₀, e₀, he₀, he₀1, henergy⟩ :=
    n07a_referenceEnergy_outer_budget hD hT href h05 hI Col hCol
  obtain ⟨d₁, d₂, hmode⟩ := n07a_actualRelativeMain_mode_bound hD hS hT h01 h02 h03 h04
    href hcur hprincipal h05 h06 hI
  let d : ℕ := 4 + max d₁ d₂
  refine ⟨d, fun t s => ?_⟩
  obtain ⟨e₁, e₂, he₁, he₂, he₁0, he₂0, hmodes⟩ := hmode s
  let e : ℕ → ℝ := fun m => e₁ m + e₂ m
  have he : N07aSampleSubpower T K e := he₁.add he₂
  have he0 (m : ℕ) : 0 ≤ e m := add_nonneg (he₁0 m) (he₂0 m)
  have he₀0 (m : ℕ) : 0 ≤ e₀ m := zero_le_one.trans (he₀1 m)
  have hprod : N07aSampleSubpower T K (fun m => e m * e₀ m) :=
    N07aSampleSubpower.mul hD hT he he₀
  obtain ⟨A, hA, hweight⟩ := hprod.volume_gain_absorption hD hT
    (by norm_num : (0 : ℝ) < 3 / 4) t (0 - B.lossMaterial)
  refine ⟨A * A₀, mul_pos hA hA₀, fun z hz j F hF hU => ?_⟩
  obtain ⟨a₀, ha₀, hnorm, hpieces⟩ := henergy j F hF hU
  let n : ℝ := parameterGrading S (s + d) z
  have hn : 0 ≤ n := apply_nonneg _ _
  let a : lp (fun _ : ℕ => ℝ) 2 := (A * n) • a₀
  have ha (m : ℕ) : a m = A * n * a₀ m := by
    simp only [a, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  refine ⟨a, fun m => by rw [ha]; exact mul_nonneg (mul_nonneg hA.le hn) (ha₀ m), ?_, ?_⟩
  · rw [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA.le hn)]
    exact (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hA.le hn)).trans_eq (by ring)
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
      simpa only [n07aAngularUnknownBand_field] using
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
        (mul_le_mul_of_nonneg_left hn₂ (he₂0 m))).trans_eq (by dsimp only [e]; ring)
    have hraw := (hmodes z hz F m j l hband commute).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (mul_nonneg hH hτ)) hE)
    have hmodeeq : n07aAngularGap j l ^ s * ‖n07aAngularBand m (hI m) l (κ • f)‖ =
        Real.sqrt (Real.pi * (K.right m - K.left m)) *
          ‖(n07aAngularGap j l ^ s * κ) • n07aCanonicalUnitMode (hI m) f l‖ := by
      have hg : 0 ≤ n07aAngularGap j l ^ s :=
        pow_nonneg (zero_le_one.trans (n07aAngularGap_one_le j l)) s
      rw [map_smul, norm_smul, n07aAngularBand_norm_unitMode (hI m) f hf l,
        norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
      ring
    have hb : n07aAngularGap j l ^ s * ‖n07aAngularBand m (hI m) l (κ • f)‖ ≤
        H * τ * (e m * n) * E := by
      rw [hmodeeq, n07aAngularGap_eq_int]
      exact hraw
    have hew : v * H * w * (e m * e₀ m) ≤ A := by
      have h := hweight m
      rw [abs_of_nonneg (mul_nonneg (he0 m) (he₀0 m))] at h
      exact h
    have hp := hpieces m
    change J * E ≤ e₀ m * w * a₀ m at hp
    rw [ha]
    change J * (v * n07aAngularGap j l ^ s *
      ‖n07aAngularBand m (hI m) l (κ • f)‖) ≤ τ * (A * n * a₀ m)
    calc
      _ ≤ J * (v * (H * τ * (e m * n) * E)) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hv) hJ
      _ = (v * H * τ * e m * n) * (J * E) := by ring
      _ ≤ (v * H * τ * e m * n) * (e₀ m * w * a₀ m) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (v * H * w * (e m * e₀ m)) * (τ * n * a₀ m) := by ring
      _ ≤ A * (τ * n * a₀ m) :=
        mul_le_mul_of_nonneg_right hew (mul_nonneg (mul_nonneg hτ hn) (ha₀ m))
      _ = _ := by ring

end ContinuousFlexibility.Analysis
