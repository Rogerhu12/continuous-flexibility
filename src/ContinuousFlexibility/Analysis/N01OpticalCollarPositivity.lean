module

public import ContinuousFlexibility.Analysis.N01CoefficientSmallness
public import ContinuousFlexibility.Analysis.N01OpticalCorrectionCutoffs
public import ContinuousFlexibility.Analysis.N01RadialFlow

/-!
# Uniform positivity on the actual optical correction collars

The reference inverse-profile bound and the selected optical-speed
lower bound yield lower bounds for both positive reference coefficients
a and -c in one radial cell weight. The actual first-variation estimate
then preserves both signs on one high-grade neighborhood. In particular
the actual characteristic discriminant is strictly positive on every
cutoff transition, without an additional positivity assumption.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01OpticalCollarPositivityStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem optical_reference_two_lower_bounds
    {E A B R w v : ℝ} (hE : 1 ≤ E) (hA : 0 < A) (hB : 0 < B)
    (hR : 0 < R) (hw : 0 < w)
    (hi : w⁻¹ ≤ A * E ^ A)
    (hv : E ^ (-B) / (2 * R) ≤ v) :
    let lam := (A * (max (2 * R) 1) ^ 2)⁻¹
    lam * E ^ (-(A + 2 * B)) ≤ w ∧
      lam * E ^ (-(A + 2 * B)) ≤ w * v ^ 2 := by
  let T := max (2 * R) 1
  let lam := (A * T ^ 2)⁻¹
  have hE₀ : 0 < E := zero_lt_one.trans_le hE
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hT₁ : 1 ≤ T := le_max_right _ _
  have hlam : 0 < lam := inv_pos.mpr (mul_pos hA (sq_pos_of_pos hT))
  have hwlow : A⁻¹ * E ^ (-A) ≤ w := by
    have hi' : (A * E ^ A)⁻¹ ≤ w := by
      apply (inv_le_iff_one_le_mul₀ (mul_pos hA (Real.rpow_pos_of_pos hE₀ _))).mpr
      simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hw).mp hi
    simpa only [mul_inv, Real.rpow_neg hE₀.le] using hi'
  have hvlow : E ^ (-B) / T ≤ v :=
    (div_le_div_of_nonneg_left (Real.rpow_nonneg hE₀.le _)
      (mul_pos (by norm_num) hR) (le_max_left _ _)).trans hv
  have hp : E ^ (-A) * (E ^ (-B)) ^ 2 = E ^ (-(A + 2 * B)) := by
    rw [pow_two, ← Real.rpow_add hE₀, ← Real.rpow_add hE₀]
    congr 1
    ring
  have hlamA : lam ≤ A⁻¹ := by
    apply (inv_le_inv₀ (mul_pos hA (sq_pos_of_pos hT)) hA).mpr
    have hT₂ : (1 : ℝ) ≤ T ^ 2 := by nlinarith only [hT₁]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT₂ hA.le
  have hEP : E ^ (-(A + 2 * B)) ≤ E ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith only [hB])
  constructor
  · exact (mul_le_mul hlamA hEP (Real.rpow_nonneg hE₀.le _)
      (inv_nonneg.mpr hA.le)).trans hwlow
  · have hs : 0 ≤ E ^ (-B) / T := div_nonneg (Real.rpow_nonneg hE₀.le _) hT.le
    have hprod := mul_le_mul hwlow
      (pow_le_pow_left₀ hs hvlow 2) (sq_nonneg _) hw.le
    calc
      lam * E ^ (-(A + 2 * B)) =
          (A⁻¹ * E ^ (-A)) * (E ^ (-B) / T) ^ 2 := by
        rw [← hp, div_pow]
        dsimp only [lam]
        rw [mul_inv]
        ring
      _ ≤ w * v ^ 2 := hprod

theorem N01Properties.reference_coefficients
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (p : PolarPoint) :
    (originalCoefficients D S C (C.referenceState, 0)).a p = D.w p.1 ∧
      (originalCoefficients D S C (C.referenceState, 0)).b p = 0 ∧
      (originalCoefficients D S C (C.referenceState, 0)).c p = deriv D.w p.1 / p.1 := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hprofile : stateProfile D S C C.referenceState = D.w := by
    funext r
    simp [stateProfile, stateKappa, href.2.2.1, href.2.2.2.1, angularMean]
  obtain ⟨_, hdata⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ (stateProfile D S C C.referenceState) := by
    rw [hprofile]
    exact hdata.1.2.2.1.1
  simpa only [hprofile] using originalCoefficients_radial_zero C.referenceState hw p

theorem profile_mul_opticalSpeed_sq
    {w : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hw : 0 < w r)
    (hwd : deriv w r ≤ 0) :
    w r * opticalSpeed w r ^ 2 = -deriv w r / r := by
  have hq : 0 ≤ -deriv w r / (r * w r) :=
    div_nonneg (neg_nonneg.mpr hwd) (mul_nonneg hr.le hw.le)
  rw [opticalSpeed, Real.sq_sqrt hq]
  field_simp [hr.ne', hw.ne']

theorem N01Properties.opticalCollar_reference_coefficient_lower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B : ℝ} (hB : 0 < B)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) :
    ∃ lam P : ℝ, 0 < lam ∧ 0 < P ∧ ∀ m p,
      p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      lam * radialE (D.cellIndex (j m)) ^ (-P) ≤
        (originalCoefficients D S C (C.referenceState, 0)).a p ∧
      lam * radialE (D.cellIndex (j m)) ^ (-P) ≤
        -(originalCoefficients D S C (C.referenceState, 0)).c p := by
  obtain ⟨A, hA, hi⟩ := hN.1.1.inverse_first_jets_cell_bound
  obtain ⟨_, hdata⟩ := hN.1.1
  have hg : RadialProfileGeometry D := hdata.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  let lam := (A * (max (2 * (D.b - D.a)) 1) ^ 2)⁻¹
  have hlam : 0 < lam := inv_pos.mpr (mul_pos hA
    (sq_pos_of_pos (zero_lt_one.trans_le (le_max_right _ _))))
  refine ⟨lam, A + 2 * B, hlam, by linarith only [hA, hB], fun m p hp => ?_⟩
  have hm : p.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
  have hr : p.1 ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hm.1, hm.2.trans (hC.1 m).2.2⟩
  have hw : 0 < D.w p.1 := hg.2.2.2.2.1 _ hr
  have hwi : (D.w p.1)⁻¹ ≤ A * radialE (D.cellIndex (j m)) ^ A := by
    calc
      _ = |(D.w p.1)⁻¹| := (abs_of_pos (inv_pos.mpr hw)).symm
      _ ≤ |(D.w p.1)⁻¹| + |deriv (fun s => (D.w s)⁻¹) p.1| :=
        le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ _ := hi (j m) p.1 (hcell m hm)
  have hE : 1 ≤ radialE (D.cellIndex (j m)) := by
    have hn : 0 ≤ (D.cellIndex (j m) : ℝ) := Nat.cast_nonneg _
    have he : 1 ≤ Real.exp 1 + (D.cellIndex (j m) : ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hn)
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))
  have h := optical_reference_two_lower_bounds hE hA hB
    (sub_pos.mpr hg.2.1) hw hwi (hspeed m p.1 hp)
  have hsquare := profile_mul_opticalSpeed_sq (hg.1.trans hr.1) hw (hC.2.2.2.1 m _ hm).le
  obtain ⟨ha, _, hc⟩ := hN.reference_coefficients p
  rw [ha, hc]
  exact ⟨h.1, h.2.trans_eq (hsquare.trans (neg_div _ _))⟩

/-- The same high-grade neighborhood works on every actual selected
collar. The discriminant bound is quantitative and retains its radial
cell weight. No state-sector premise is needed for these coefficient
signs. -/
theorem N01Properties.opticalCollar_uniform_positive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B : ℝ} (hB : 0 < B)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) :
    ∃ base' : ℕ, ∃ ε' lam P : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < lam ∧ 0 < P ∧
      N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ Icc (x m - δ m) (x m + δ m) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        d ≤ (originalCoefficients D S C z).a p ∧
        d ≤ -(originalCoefficients D S C z).c p ∧
        d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨lam, P, hlam, hP, href⟩ :=
    hN.opticalCollar_reference_coefficient_lower j x δ hB hcell hinside hspeed
  obtain ⟨K, hK, hsmall⟩ := hN.coefficientFamily_radial_small hT 0 hP.le
  let base' := max base loss
  let ε' := min ε (min (1 / 2) (lam / (4 * K)))
  have hε' : 0 < ε' := lt_min hN.2.1 (lt_min (by norm_num) (div_pos hlam (by positivity)))
  have hεε : ε' ≤ ε := min_le_left _ _
  have hεhalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεK : K * ε' ≤ lam / 4 := by
    have hεl : ε' ≤ lam / (4 * K) := (min_le_right _ _).trans (min_le_right _ _)
    calc
      _ ≤ K * (lam / (4 * K)) := mul_le_mul_of_nonneg_left hεl hK.le
      _ = lam / 4 := by field_simp [hK.ne']
  refine ⟨base', ε', lam, P, le_max_left _ _, hε', hεε, hlam, hP,
    hN.restrict_neighborhood hT (le_max_left _ _) hε' hεε,
    fun z hz m p hp => ?_⟩
  have hm : p.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
  have hbase : base ≤ base' := le_max_left _ _
  have hhigh : 0 + loss ≤ base' := by simpa only [zero_add] using le_max_right base loss
  have ha₀ := hsmall base' hbase hhigh ε' hε'.le hεε hεhalf z hz
    (j m) (0 : Fin 3) 0 0 p (by norm_num) (hcell m hm)
  have hc₀ := hsmall base' hbase hhigh ε' hε'.le hεε hεhalf z hz
    (j m) (2 : Fin 3) 0 0 p (by norm_num) (hcell m hm)
  have hfa : coefficientFamily D S C (0 : Fin 3) 0 0 p z =
      (originalCoefficients D S C z).a p -
        (originalCoefficients D S C (C.referenceState, 0)).a p := by
    simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero]
    rfl
  have hfc : coefficientFamily D S C (2 : Fin 3) 0 0 p z =
      (originalCoefficients D S C z).c p -
        (originalCoefficients D S C (C.referenceState, 0)).c p := by
    simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero]
    rfl
  rw [hfa] at ha₀
  rw [hfc] at hc₀
  let e := radialE (D.cellIndex (j m)) ^ (-P)
  have he : 0 < e := Real.rpow_pos_of_pos (Real.exp_pos _) _
  change |(originalCoefficients D S C z).a p -
    (originalCoefficients D S C (C.referenceState, 0)).a p| ≤ K * ε' * e at ha₀
  change |(originalCoefficients D S C z).c p -
    (originalCoefficients D S C (C.referenceState, 0)).c p| ≤ K * ε' * e at hc₀
  have her : K * ε' * e ≤ lam * e / 4 := by
    have h := mul_le_mul_of_nonneg_right hεK he.le
    linarith only [h]
  have ha := (abs_le.mp ha₀).1
  have hc := (abs_le.mp hc₀).2
  obtain ⟨har, hcr⟩ := href m p hp
  change lam * e ≤ (originalCoefficients D S C (C.referenceState, 0)).a p at har
  change lam * e ≤ -(originalCoefficients D S C (C.referenceState, 0)).c p at hcr
  have hapos : lam * e / 2 ≤ (originalCoefficients D S C z).a p := by
    linarith only [ha, har, her, mul_pos hlam he]
  have hcneg : lam * e / 2 ≤ -(originalCoefficients D S C z).c p := by
    linarith only [hc, hcr, her, mul_pos hlam he]
  refine ⟨hapos, hcneg, ?_⟩
  have hd : 0 ≤ lam * e / 2 := div_nonneg (mul_nonneg hlam.le he.le) (by norm_num)
  have hprod := mul_le_mul hapos hcneg hd (hd.trans hapos)
  nlinarith only [hprod, sq_nonneg ((originalCoefficients D S C z).b p)]


/-- Keep every witness of the actual optical collar selection. In particular
all later estimates use the same cutoff, its actual radial cell and its
actual center and width. The quantitative positivity holds on the full
closed collar, including the endpoints of the transition support. -/
theorem N01Properties.exists_positive_opticalCorrectionCollars
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ, ∃ j : ℕ → ℕ,
      ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
        0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
        (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
        ∀ r ∈ Icc (x m - δ m) (x m + δ m),
          radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
      (∀ m, χ m = returnOpticalCutoff (x m) (δ m)) ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m)) ∧
      (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ Icc (x m - δ m) (x m + δ m) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        0 < d ∧
        d ≤ (originalCoefficients D S C z).a p ∧
        d ≤ -(originalCoefficients D S C z).c p ∧
        d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨K, A, B, hK, hA, hB, j, x, δ, χ, hdata, hχeq, hχ, hend, hjets⟩ :=
    hN.exists_opticalCorrectionCutoffs
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) := (hdata m).1
  have hinside (m : ℕ) :
      C.left m < x m - δ m ∧ x m + δ m < C.right m :=
    ⟨(hdata m).2.2.1, (hdata m).2.2.2.1⟩
  have hspeed (m : ℕ) (r : ℝ) (hr : r ∈ Icc (x m - δ m) (x m + δ m)) :
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r :=
    (hdata m).2.2.2.2.2 r hr
  obtain ⟨base', ε', lam, P, hb, hε', hεε, hlam, hP, hnew, hpos⟩ :=
    hN.opticalCollar_uniform_positive hT j x δ hB hcell hinside hspeed
  refine ⟨base', ε', χ, j, x, δ, K, A, B, lam, P, hb, hε', hεε,
    hK, hA, hB, hlam, hP, hnew, hdata, hχeq, hχ, hend, hjets, ?_⟩
  intro z hz m p hp
  have hb := hpos z hz m p hp
  have hd : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
    div_pos (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)) (by norm_num)
  exact ⟨hd, hb.1, hb.2.1, hb.2.2, (sq_pos_of_pos hd).trans_le hb.2.2⟩

/-- The correction cutoff family and the common neighborhood are both
constructed from the original N01 data. The actual discriminant is
positive on the entire closed support of each transition derivative,
and all cutoff jets retain uniform radial-power estimates. -/
theorem N01Properties.exists_positive_opticalCorrectionCutoffs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ, ∃ j : ℕ → ℕ,
      ∃ A lam P : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < A ∧ 0 < lam ∧ 0 < P ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m)) ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
      (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ tsupport (deriv (χ m)) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        0 < d ∧
        d ≤ (originalCoefficients D S C z).a p ∧
        d ≤ -(originalCoefficients D S C z).c p ∧
        d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨K, A, B, hK, hA, hB, j, x, δ, χ, hdata, hχeq, hχ, hend, hjets⟩ :=
    hN.exists_opticalCorrectionCutoffs
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) := (hdata m).1
  have hinside (m : ℕ) :
      C.left m < x m - δ m ∧ x m + δ m < C.right m :=
    ⟨(hdata m).2.2.1, (hdata m).2.2.2.1⟩
  have hspeed (m : ℕ) (r : ℝ) (hr : r ∈ Icc (x m - δ m) (x m + δ m)) :
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r :=
    (hdata m).2.2.2.2.2 r hr
  obtain ⟨base', ε', lam, P, hbase, hε', hεε, hlam, hP, hnew, hpos⟩ :=
    hN.opticalCollar_uniform_positive hT j x δ hB hcell hinside hspeed
  refine ⟨base', ε', χ, j, A, lam, P, hbase, hε', hεε, hA, hlam, hP,
    hnew, hcell, hχ, ?_, hjets, ?_⟩
  · intro m
    refine ⟨(hend m).1, (hend m).2.1, fun r hr => ?_⟩
    have hr' := (hend m).2.2 hr
    exact ⟨(hinside m).1.trans_le hr'.1, hr'.2.trans_lt (hinside m).2⟩
  · intro z hz m p hp
    have hb := hpos z hz m p ((hend m).2.2 hp)
    have hd : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
      div_pos (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)) (by norm_num)
    exact ⟨hd, hb.1, hb.2.1, hb.2.2, (sq_pos_of_pos hd).trans_le hb.2.2⟩


end ContinuousFlexibility.Statements

