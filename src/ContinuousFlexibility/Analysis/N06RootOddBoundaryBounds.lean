module

public import ContinuousFlexibility.Analysis.N06PhysicalRootLogHeight
public import ContinuousFlexibility.Analysis.N06PositiveLogFiniteJets
public import ContinuousFlexibility.Analysis.N06RootLabelJets
public import ContinuousFlexibility.Analysis.N06MaterialAbsorption

/-!
# Weighted angular jets of the true root odd-field logarithm

At radial order zero the common reference speed factor cancels from the
current/reference logarithmic difference. The remaining factors are the
actual physical speed ratio and the derivative of the original left
label. Both have positive lower bounds from N01, so their finite angular
logarithmic jets retain their actual small weighted differences.

The physical root weight and the label sample weight remain separate.
No relation between their cell labels, no reference root-factor lower
bound, and no uniform bound on an arbitrary angular gauge is assumed.
This file addresses radial order zero; higher radial orders also involve
the relative radial jets of the fixed reference speed factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

namespace N04bRootCoordinateProperties

/-- The actual divided odd value has a common positive reference factor.
That factor cancels before taking any angular derivatives. -/
theorem n06_logOdd_boundary_eq_normalized
    {d c d₀ c₀ : PolarPoint → ℝ} {β : ℝ → ℝ}
    {Φ Φ₀ : ℝ → ℝ → ℝ} {R R₀ σ σ₀ : ℝ}
    {G G₀ : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    (P₀ : N04bRootCoordinateProperties d₀ c₀ (fun t => t) Φ₀ R₀ σ₀ G₀)
    {a : ℝ} (ha : 0 < a) {s : ℝ → ℝ} (hs : ∀ θ, 0 < s θ)
    (hc : ∀ θ, c (0, θ) = a * s θ) (hc₀ : ∀ θ, c₀ (0, θ) = a) (θ : ℝ) :
    Real.log (extendedRootOddCoefficient G (0, θ)) -
        Real.log (extendedRootOddCoefficient G₀ (0, θ)) =
      Real.log (s θ) + Real.log (deriv β θ) := by
  have hO : extendedRootOddCoefficient G (0, θ) =
      ((2 / 3 : ℝ) * a) * (s θ * deriv β θ) := by
    rw [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ)), P.odd_zero θ, hc θ]
    ring
  have hO₀ : extendedRootOddCoefficient G₀ (0, θ) = (2 / 3 : ℝ) * a := by
    rw [extendedRootOddCoefficient_of_nonneg G₀ (le_refl (0 : ℝ)), P₀.odd_zero θ, hc₀ θ]
    simp only [deriv_id'', mul_one]
  have ha' : 0 < (2 / 3 : ℝ) * a := mul_pos (by norm_num) ha
  rw [hO, hO₀, Real.log_mul ha'.ne' (mul_pos (hs θ) (P.label_positive θ)).ne',
    Real.log_mul (hs θ).ne' (P.label_positive θ).ne']
  ring

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- N01 supplies a fixed positive normalization of the actual speed
ratio, independently of the size of its reference root factor. -/
theorem n06_physicalRootSpeedRatio_lower
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    (1 / 2 : ℝ) ≤ (n06PhysicalRootFields D S C z (r, θ)).2 := by
  let Δ : ℝ := polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) (r, θ)
  let q : ℝ := heightQ (profileEnergy (stateProfile D S C z.1) (r, θ))
    (heightRadial (stateHeight D S C z) (r, θ))
    (angularPartial (heightAngular (stateHeight D S C z)) (r, θ))
  have h := hN.2.2.2.2.2.2.2.2.2.1 z hz hs (r, θ) ⟨hr, mem_univ θ⟩
  have hprofile : stateProfile D S C z.1 r = D.w r :=
    (hN.2.2.2.2.2.2.2.2.2.2.1 z hz r hr hroot).eq_of_nhds
  have hQlo : (7 / 8 : ℝ) ≤ q / D.w r := by
    simpa only [q, hprofile] using h.2.2.1
  have hQhi : q / D.w r ≤ (9 / 8 : ℝ) := by
    simpa only [q, hprofile] using h.2.2.2.1
  have hΔ : (1 / 2 : ℝ) ≤ Δ := h.2.2.2.2.1
  have hQpos : 0 < q / D.w r := lt_of_lt_of_le (by norm_num) hQlo
  have hsqrt : (5 / 8 : ℝ) ≤ Real.sqrt Δ := Real.le_sqrt_of_sq_le (by nlinarith)
  have he : (n06PhysicalRootFields D S C z (r, θ)).2 = Real.sqrt Δ / (q / D.w r) := by
    change D.w r * Real.sqrt Δ / q = Real.sqrt Δ / (q / D.w r)
    rw [div_div_eq_mul_div, mul_comm (D.w r)]
  rw [he]
  exact (le_div_iff₀ hQpos).mpr (by nlinarith)

def N06PhysicalRootLogSpeedAngularBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ, ∀ k, k ≤ n →
      |iteratedDeriv k (fun t => Real.log
        (n06PhysicalRootFields D S C z (r, t)).2) θ| ≤
          Q * n06RootJetWeight T (r, θ) * |z.2|

def N06StateLeftChartLogDerivBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 2) (z.1 - C.referenceState) ≤ 1 →
    ∀ m θ k, k ≤ n →
      |iteratedDeriv k (fun t => Real.log (deriv (stateLeftChart S z.1 m) t)) θ| ≤
        Q * T.H (T.sample m) ^ (3 / 4 : ℝ) *
          stateGrading S (n + 2) (z.1 - C.referenceState)

/-- Every fixed angular log-speed jet is uniformly small at every actual
turning root, with the physical material weight still present. -/
private theorem n06_physicalRootLogSpeed_named
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06PhysicalRootLogSpeedAngularBound D T S C base n ε Q := by
  obtain ⟨A, hA, hphysical⟩ := n06_physicalRootFields_finite_weighted_jets hT hS hN n
  obtain ⟨H, hH, hweight⟩ :=
    n06_material_loss_absorb hT (3 / 4 : ℝ) 0 1 (by norm_num)
  obtain ⟨Q, hQ, hlog⟩ := n06_log_finite_jets_of_one_difference n (mul_nonneg hA hH.le)
  refine ⟨Q * A, mul_nonneg hQ hA, ?_⟩
  intro z hz hs hsmall r hr hroot θ k hk
  let f : ℝ → ℝ := fun t => (n06PhysicalRootFields D S C z (r, t)).2
  have hf : ContDiffAt ℝ ∞ f θ :=
    (n06_physicalRootFields_contDiffAt_root hT hS hN hz hs hr hroot θ).snd.comp θ
      (contDiffAt_const.prodMk contDiffAt_id)
  have hW : 0 ≤ n06RootJetWeight T (r, θ) := n06_rootJetWeight_nonneg hT ⟨hr, mem_univ θ⟩
  have hWH : n06RootJetWeight T (r, θ) ≤ H := by
    simpa only [n06RootJetWeight, Real.rpow_zero, Real.rpow_one, mul_one] using hweight r hr
  have hq : |z.2| ≤ 1 := (le_add_of_nonneg_left
    (apply_nonneg (stateGrading S (n + 7)) (z.1 - C.referenceState))).trans hsmall
  have hδ : 0 ≤ A * n06RootJetWeight T (r, θ) * |z.2| :=
    mul_nonneg (mul_nonneg hA hW) (abs_nonneg _)
  have hδB : A * n06RootJetWeight T (r, θ) * |z.2| ≤ A * H := by
    calc
      _ ≤ A * n06RootJetWeight T (r, θ) * 1 :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hA hW)
      _ ≤ A * H := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hWH hA
  have hdiff (j : ℕ) (hj : j ≤ n) : |iteratedDeriv j (fun t => f t - 1) θ| ≤
      A * n06RootJetWeight T (r, θ) * |z.2| := by
    have hD := n06_physicalRootDifference_contDiffAt_root hT hS hN hz hs hr hroot θ
    have hslice := n06_angularSlice_iteratedDeriv_le hD.snd j
    change |iteratedDeriv j (fun t => f t - 1) θ| ≤
      ‖iteratedFDeriv ℝ j (fun p => (n06PhysicalRootDifference D S C z p).2) (r, θ)‖ at hslice
    exact (hslice.trans (n06_norm_iteratedFDeriv_snd_le hD j)).trans
      (hphysical z hz hs hsmall r hr hroot θ j hj)
  have h := hlog f θ (A * n06RootJetWeight T (r, θ) * |z.2|) hf
    (n06_physicalRootSpeedRatio_lower hN hz hs hr hroot θ) hδ hδB hdiff k hk
  exact h.trans_eq (by ring)

theorem n06_physicalRootLogSpeed_angular_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
      ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ, ∀ k, k ≤ n →
        |iteratedDeriv k (fun t => Real.log
          (n06PhysicalRootFields D S C z (r, t)).2) θ| ≤
            Q * n06RootJetWeight T (r, θ) * |z.2| := by
  exact n06_physicalRootLogSpeed_named hT hS hN n

/-- The original left label, including all its finite angular jets,
has a logarithmic derivative difference with its true sample weight. -/
private theorem n06_stateLeftChart_logDeriv_named
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06StateLeftChartLogDerivBound T S C base n ε Q := by
  obtain ⟨H, hH, hweight⟩ :=
    n06_material_loss_absorb hT (3 / 4 : ℝ) 0 0 (by norm_num)
  obtain ⟨Q, hQ, hlog⟩ := n06_log_finite_jets_of_one_difference n
    (mul_nonneg anglePairEvaluationConstant_nonneg hH.le)
  refine ⟨Q * anglePairEvaluationConstant,
    mul_nonneg hQ anglePairEvaluationConstant_nonneg, ?_⟩
  intro z hz hs hsmall m θ k hk
  let f : ℝ → ℝ := deriv (stateLeftChart S z.1 m)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_infty_iff_deriv.mp (contDiff_stateLeftChart hS z.1 m)).2
  have hsample : T.sample m ∈ radialCore D :=
    materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hW : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 _ hsample).2.1.le _
  have hWH : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hweight _ hsample
  let δ : ℝ := (anglePairEvaluationConstant * stateGrading S (n + 2)
    (z.1 - C.referenceState)) * T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hδ : 0 ≤ δ := mul_nonneg
    (mul_nonneg anglePairEvaluationConstant_nonneg (apply_nonneg _ _)) hW
  have hδB : δ ≤ anglePairEvaluationConstant * H := by
    calc
      δ ≤ (anglePairEvaluationConstant * 1) * T.H (T.sample m) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmall anglePairEvaluationConstant_nonneg) hW
      _ ≤ anglePairEvaluationConstant * H := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hWH anglePairEvaluationConstant_nonneg
  have hdiff (j : ℕ) (hj : j ≤ n) :
      |iteratedDeriv j (fun t => f t - 1) θ| ≤ δ := by
    have h := n06_stateLeftChart_boundary_label_jets hN.1.1 hT hS hN.2.2.1
      (n + 1) z.1 m (j + 1) (by omega) θ
    simp only [iteratedDeriv_succ', deriv_id''] at h
    have he := iteratedDeriv_fun_sub
      (hf.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      (contDiffAt_const : ContDiffAt ℝ (j : ℕ∞ω) (fun _ : ℝ => (1 : ℝ)) θ)
    exact (congrArg abs he).trans_le h
  have hpositive : (1 / 2 : ℝ) ≤ f θ :=
    (hN.2.2.2.2.2.2.2.1 z hz hs m θ).1
  have h := hlog f θ δ hf.contDiffAt hpositive hδ hδB hdiff k hk
  exact h.trans_eq (by dsimp only [δ]; ring)

theorem n06_stateLeftChart_logDeriv_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (n + 2) (z.1 - C.referenceState) ≤ 1 →
      ∀ m θ k, k ≤ n →
        |iteratedDeriv k (fun t => Real.log (deriv (stateLeftChart S z.1 m) t)) θ| ≤
          Q * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            stateGrading S (n + 2) (z.1 - C.referenceState) := by
  exact n06_stateLeftChart_logDeriv_named hT hS hN n

private theorem n06_rootOdd_seminorm_center
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

private theorem n06_rootOdd_reference_neighborhood
    (hN : N01Properties D T S C base loss ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · exact n06_rootOdd_seminorm_center (stateGrading S base) C.referenceState hN.2.1
  · simpa only [abs_zero] using hN.2.1

/-- Exact cancellation for two actual root-coordinate witnesses.
Their primitive speed germs need only be identified on the boundary.
The reference witness uses the actual reference label, namely identity. -/
theorem n06_N01_leftRoot_logOdd_boundary_identity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (m : ℕ) (ι : ℝ) {g : ℝ → ℝ} (hg : 0 < g 0)
    {d c d₀ c₀ : PolarPoint → ℝ} {Φ Φ₀ : ℝ → ℝ → ℝ}
    {R R₀ σ σ₀ : ℝ} {G G₀ : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c (stateLeftChart S z.1 m) Φ R σ G)
    (P₀ : N04bRootCoordinateProperties d₀ c₀ (fun t => t) Φ₀ R₀ σ₀ G₀)
    (hc : ∀ θ, c (0, θ) = factoredCharacteristicSpeed D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r ι (0, θ))
    (hc₀ : ∀ θ, c₀ (0, θ) = factoredCharacteristicSpeed D.w g
      (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) r ι (0, θ)) :
    (fun θ => Real.log (extendedRootOddCoefficient G (0, θ)) -
      Real.log (extendedRootOddCoefficient G₀ (0, θ))) =
    fun θ => Real.log (n06PhysicalRootFields D S C z (r, θ)).2 +
      Real.log (deriv (stateLeftChart S z.1 m) θ) := by
  let a : ℝ := referenceRootSpeedFactor D.w g r ι 0
  have hw : 0 < D.w r := hN.1.1.choose_spec.1.2.2.2.2.1 r hr
  have ha : 0 < a := referenceRootSpeedFactor_pos
    (w := D.w) (g := g) (r := r) (σ := ι) (t := 0)
    (by simpa only [mul_zero, add_zero] using hN.1.1.choose_spec.1.1.trans hr.1)
    (by simpa only [mul_zero, add_zero] using hw) hg
  have hfactor (x : AnnularState S × ℝ) (θ : ℝ) :
      factoredCharacteristicSpeed D.w g (stateProfile D S C x.1)
        (stateHeight D S C x) r ι (0, θ) =
          a * (n06PhysicalRootFields D S C x (r, θ)).2 := by
    have h := (n06_factoredRootFields_eq_physical D S C x g r ι (0, θ)
      (by simpa only [n06_rootProfileShift_boundary] using hw.ne')).2
    simpa only [n06_rootProfileShift_boundary] using h
  have hzero (θ : ℝ) :
      (n06PhysicalRootFields D S C (C.referenceState, 0) (r, θ)).2 = 1 := by
    have he := (n06_physicalRootFields_germ_eq_absorbed hT hS hN
      (n06_rootOdd_reference_neighborhood hN) hr hroot θ).eq_of_nhds
    have hz := congrFun (n06_rootAbsorbedFields_zero_parameter D S C.referenceState) (r, θ)
    have hpair : n06PhysicalRootFields D S C (C.referenceState, 0) (r, θ) = (0, 1) :=
      he.trans hz
    simpa only [] using congrArg Prod.snd hpair
  have hc' (θ : ℝ) : c (0, θ) = a * (n06PhysicalRootFields D S C z (r, θ)).2 :=
    (hc θ).trans (hfactor z θ)
  have hc₀' (θ : ℝ) : c₀ (0, θ) = a := by
    rw [hc₀ θ, hfactor (C.referenceState, 0) θ, hzero θ, mul_one]
  funext θ
  exact P.n06_logOdd_boundary_eq_normalized P₀ ha
    (fun t => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (n06_physicalRootSpeedRatio_lower hN hz hs hr hroot t)) hc' hc₀' θ

def N06LeftRootOddLogBoundaryBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ m : ℕ, ∀ ι : ℝ, ∀ g : ℝ → ℝ, 0 < g 0 →
    ∀ (d c d₀ c₀ : PolarPoint → ℝ) (Φ Φ₀ : ℝ → ℝ → ℝ)
      (R R₀ σ σ₀ : ℝ) (G G₀ : ℝ × ℝ × ℝ → ℝ),
    N04bRootCoordinateProperties d c (stateLeftChart S z.1 m) Φ R σ G →
    N04bRootCoordinateProperties d₀ c₀ (fun t => t) Φ₀ R₀ σ₀ G₀ →
    (∀ θ, c (0, θ) = factoredCharacteristicSpeed D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r ι (0, θ)) →
    (∀ θ, c₀ (0, θ) = factoredCharacteristicSpeed D.w g
      (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) r ι (0, θ)) →
    ∀ θ : ℝ, ∀ k, k ≤ n →
      |iteratedDeriv k (fun t => Real.log (extendedRootOddCoefficient G (0, t)) -
        Real.log (extendedRootOddCoefficient G₀ (0, t))) θ| ≤
      Q * (n06RootJetWeight T (r, θ) * |z.2| +
        T.H (T.sample m) ^ (3 / 4 : ℝ) * stateGrading S (n + 7) (z.1 - C.referenceState))

private theorem n06_rootOdd_sum_jet_bound
    {f g : ℝ → ℝ} {θ A B X Y : ℝ} (k : ℕ)
    (hf : ContDiffAt ℝ ∞ f θ) (hg : ContDiffAt ℝ ∞ g θ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hfj : |iteratedDeriv k f θ| ≤ A * X)
    (hgj : |iteratedDeriv k g θ| ≤ B * Y) :
    |iteratedDeriv k (fun t => f t + g t) θ| ≤ (A + B) * (X + Y) := by
  rw [iteratedDeriv_fun_add (hf.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (k : ℕ∞ω) ≤ ∞))]
  apply (abs_add_le _ _).trans
  apply (add_le_add hfj hgj).trans
  nlinarith only [mul_nonneg hA hY, mul_nonneg hB hX]

/-- Keep the scalar estimate independent of both root-coordinate witnesses.
The final coordinate identification below then transports only one real
inequality, without rewriting inside the entire N01/N04 context. -/
private theorem n06_leftRoot_logSpeed_add_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspeed : N06PhysicalRootLogSpeedAngularBound D T S C base n ε A)
    (hlabel : N06StateLeftChartLogDerivBound T S C base n ε B)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hsmall : stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (m : ℕ) (θ : ℝ) (k : ℕ) (hk : k ≤ n) :
    |iteratedDeriv k (fun t => Real.log
        (n06PhysicalRootFields D S C z (r, t)).2 +
      Real.log (deriv (stateLeftChart S z.1 m) t)) θ| ≤
      (A + B) * (n06RootJetWeight T (r, θ) * |z.2| +
        T.H (T.sample m) ^ (3 / 4 : ℝ) *
          stateGrading S (n + 7) (z.1 - C.referenceState)) := by
  have hspeedSmooth : ContDiffAt ℝ ∞ (fun t => Real.log
      (n06PhysicalRootFields D S C z (r, t)).2) θ :=
    ((n06_physicalRootFields_contDiffAt_root hT hS hN hz hs hr hroot θ).snd.comp θ
      (contDiffAt_const.prodMk contDiffAt_id)).log
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (n06_physicalRootSpeedRatio_lower hN hz hs hr hroot θ)).ne'
  have hlabelSmooth : ContDiffAt ℝ ∞ (fun t =>
      Real.log (deriv (stateLeftChart S z.1 m) t)) θ :=
    ((contDiff_infty_iff_deriv.mp (contDiff_stateLeftChart hS z.1 m)).2.contDiffAt).log
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hN.2.2.2.2.2.2.2.1 z hz hs m θ).1).ne'
  have hgrade : stateGrading S (n + 2) (z.1 - C.referenceState) ≤
      stateGrading S (n + 7) (z.1 - C.referenceState) :=
    solve_stateGrading_monotone S (by omega) _
  have hgradeOne : stateGrading S (n + 2) (z.1 - C.referenceState) ≤ 1 :=
    hgrade.trans ((le_add_of_nonneg_right (abs_nonneg z.2)).trans hsmall)
  have hsample : T.sample m ∈ radialCore D :=
    materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hW : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 _ hsample).2.1.le _
  have hphysicalWeight : 0 ≤ n06RootJetWeight T (r, θ) * |z.2| :=
    mul_nonneg (n06_rootJetWeight_nonneg hT ⟨hr, mem_univ θ⟩) (abs_nonneg _)
  have hlabelWeight : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) *
      stateGrading S (n + 7) (z.1 - C.referenceState) := mul_nonneg hW (apply_nonneg _ _)
  have hL : |iteratedDeriv k (fun t =>
      Real.log (deriv (stateLeftChart S z.1 m) t)) θ| ≤
      B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
        stateGrading S (n + 7) (z.1 - C.referenceState) :=
    (hlabel z hz hs hgradeOne m θ k hk).trans
    (mul_le_mul_of_nonneg_left hgrade (mul_nonneg hB hW))
  apply n06_rootOdd_sum_jet_bound k hspeedSmooth hlabelSmooth hA hB
    hphysicalWeight hlabelWeight
  · simpa only [mul_assoc] using hspeed z hz hs hsmall r hr hroot θ k hk
  · simpa only [mul_assoc] using hL

/-- One constant precedes all states, roots, labels and actual flow
witnesses. No reference speed-factor cost survives at radial order zero. -/
private theorem n06_leftRootOdd_log_boundary_from_bounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspeed : N06PhysicalRootLogSpeedAngularBound D T S C base n ε A)
    (hlabel : N06StateLeftChartLogDerivBound T S C base n ε B) :
    N06LeftRootOddLogBoundaryBound D T S C base n ε (A + B) := by
  intro z hz hs hsmall r hr hroot m ι g hg d c d₀ c₀ Φ Φ₀ R R₀ σ σ₀ G G₀ P P₀ hc hc₀ θ k hk
  have he :
      (fun t => Real.log (extendedRootOddCoefficient G (0, t)) -
        Real.log (extendedRootOddCoefficient G₀ (0, t))) =
      (fun t => Real.log (n06PhysicalRootFields D S C z (r, t)).2 +
        Real.log (deriv (stateLeftChart S z.1 m) t)) :=
    n06_N01_leftRoot_logOdd_boundary_identity hT hS hN hz hs hr hroot m ι hg P P₀ hc hc₀
  exact (congrArg (fun f : ℝ → ℝ => |iteratedDeriv k f θ|) he).trans_le
    (n06_leftRoot_logSpeed_add_bound hT hS hN n hA hB hspeed hlabel
      hz hs hsmall hr hroot m θ k hk)

theorem n06_N01_leftRootOdd_log_boundary_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06LeftRootOddLogBoundaryBound D T S C base n ε Q := by
  obtain ⟨A, hA, hspeed⟩ := n06_physicalRootLogSpeed_named hT hS hN n
  obtain ⟨B, hB, hlabel⟩ := n06_stateLeftChart_logDeriv_named hT hS hN n
  exact ⟨A + B, add_nonneg hA hB,
    n06_leftRootOdd_log_boundary_from_bounds hT hS hN n hA hB hspeed hlabel⟩

end ContinuousFlexibility.Statements
