module

public import ContinuousFlexibility.Analysis.N01aOpticalControls
public import ContinuousFlexibility.Radial.DeepTailPhysicalCoefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Optical controls from the actual radial-reference hypotheses

The accumulating-profile estimates bound the derivatives of the optical
radicand on each physical cell. Continuity extends those bounds to the
endpoints of any component hosted there. The first sine margin gives a
lower bound for the actual travel with the same host-cell weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Real
open scoped ContDiff Topology

theorem n01aOpticalRadicand_cell_jets {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m →
      |iteratedDeriv s (n01aOpticalRadicand D.w) r| ≤ B * radialE (D.cellIndex m) ^ B := by
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hfinite, hlocal, hdist,
    hlower, hwjets, hinvjets, hwidth, habsorb, htrace⟩ := hD
  let E : ℕ → ℝ := fun m => radialE (D.cellIndex m)
  have hE : ∀ m, 1 ≤ E m := fun m =>
    one_le_exp_iff.mpr (Radial.radialQ_nonneg (D.cellIndex m))
  have hOne : ∀ m : ℕ, 0 ≤ (1 : ℝ) := fun _ => zero_le_one
  have hcore : ∀ m r, r ∈ D.cells m → r ∈ radialCore D :=
    fun m r hr => hpart.2.2.2.1 m hr
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hw' : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hpos : ∀ r ∈ radialCore D, 0 < D.w r := hgeom.2.2.2.2.1
  have hW (k : ℕ) : Radial.PhysicalCellBound D.cells E (fun _ => 1) (iteratedDeriv k D.w) := by
    refine ⟨C k, hC k, fun m r hr => ?_⟩
    simp only [mul_one]
    have hj : |iteratedDeriv k D.w r| ≤ C k *
        exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C k * (D.cellIndex m : ℝ) ^ 2) := by
      simpa only [Radial.radialJet_eq_iteratedDeriv] using hwjets m r hr k
    apply hj.trans
    apply mul_le_mul_of_nonneg_left _ (hC k).le
    change exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C k * (D.cellIndex m : ℝ) ^ 2) ≤
      radialE (D.cellIndex m) ^ C k
    rw [radialE, ← exp_mul]
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (Radial.radial_nat_sq_le_Q (D.cellIndex m)) (hC k).le
    have hp : 0 ≤ (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hInvW (k : ℕ) : Radial.PhysicalCellBound D.cells E (fun _ => 1)
      (iteratedDeriv k (fun r => (D.w r)⁻¹)) := by
    refine ⟨C k, hC k, fun m r hr => ?_⟩
    simpa only [Radial.radialJet_eq_iteratedDeriv, mul_one] using hinvjets m r hr k
  have hInvR (k : ℕ) : Radial.PhysicalCellBound D.cells E (fun _ => 1)
      (iteratedDeriv k (fun r : ℝ => r⁻¹)) := by
    obtain ⟨K, hK⟩ := Radial.physical_inverseRadius_jets (b := D.b) hgeom.1 k
    exact Radial.physicalCellBound_of_uniform hE
      (fun m r hr => hK r ⟨(hcore m r hr).1.le, (hcore m r hr).2.le⟩)
  have hprod (k : ℕ) : Radial.PhysicalCellBound D.cells E (fun _ => 1)
      (iteratedDeriv k (fun r => deriv D.w r * r⁻¹)) :=
    Radial.physicalCellBound_iteratedDeriv_mul hE hOne k
      (fun m r hr => hw'.contDiffAt)
      (fun m r hr => contDiffAt_id.inv (hgeom.1.trans (hcore m r hr).1).ne')
      (fun j hj => by simpa only [← iteratedDeriv_succ'] using hW (j + 1))
      (fun j hj => hInvR j)
  have hprodAt (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) :
      ContDiffAt ℝ ∞ (fun x => deriv D.w x * x⁻¹) r :=
    hw'.contDiffAt.mul (contDiffAt_id.inv (hgeom.1.trans (hcore m r hr).1).ne')
  have hInvAt (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) :
      ContDiffAt ℝ ∞ (fun x => (D.w x)⁻¹) r :=
    hw.contDiffAt.inv (hpos r (hcore m r hr)).ne'
  have hboth := Radial.physicalCellBound_iteratedDeriv_mul hE hOne s hprodAt hInvAt
    (fun j hj => hprod j) (fun j hj => hInvW j)
  obtain ⟨B, hB, hb⟩ := hboth.const_mul hE hOne (-1)
  have heq : n01aOpticalRadicand D.w =
      fun r => (-1 : ℝ) * ((deriv D.w r * r⁻¹) * (D.w r)⁻¹) := by
    funext r
    simp only [n01aOpticalRadicand, div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨B, hB, fun m r hr => ?_⟩
  rw [heq, iteratedDeriv_const_mul_field]
  simpa only [mul_one] using hb m r hr

theorem continuousOn_iteratedDeriv_n01aOpticalRadicand {D : ReferenceData}
    (hD : RadialProfileGeometry D) (s : ℕ) :
    ContinuousOn (iteratedDeriv s (n01aOpticalRadicand D.w)) (radialCore D) := by
  have hopen : IsOpen (radialCore D) := isOpen_Ioo
  have hsmooth : ContDiffOn ℝ ∞ (n01aOpticalRadicand D.w) (radialCore D) :=
    fun r hr => (contDiffAt_n01aOpticalRadicand hD.2.2.1.1
      (hD.1.trans hr.1).ne' (hD.2.2.2.2.1 r hr).ne').contDiffWithinAt
  have hc := hsmooth.continuousOn_iteratedDerivWithin (m := s) (by simp) hopen.uniqueDiffOn
  exact hc.congr (fun r hr => (iteratedDerivWithin_of_isOpen hopen hr).symm)

/-- The host cell need only contain the open component. The jet estimate
extends to both endpoints by continuity of the actual derivatives. -/
theorem n01aOpticalRadicand_component_jets {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ l h m, NegativeRadialComponent D l h → Ioo l h ⊆ D.cells m →
      ∀ r ∈ Icc l h, |iteratedDeriv s (n01aOpticalRadicand D.w) r| ≤
        B * radialE (D.cellIndex m) ^ B := by
  obtain ⟨B, hB, hb⟩ := n01aOpticalRadicand_cell_jets hD s
  obtain ⟨C, hprofile⟩ := hD
  have hc := (continuousOn_iteratedDeriv_n01aOpticalRadicand hprofile.1 s).abs
  refine ⟨B, hB, fun l h m hcomp hhost r hr => ?_⟩
  have hsub : Icc l h ⊆ radialCore D := fun x hx =>
    ⟨hcomp.1.trans_le hx.1, hx.2.trans_lt hcomp.2.2.1⟩
  have hclosure : ContinuousOn (fun x => |iteratedDeriv s (n01aOpticalRadicand D.w) x|)
      (closure (Ioo l h)) := by
    rw [closure_Ioo hcomp.2.1.ne]
    exact hc.mono hsub
  exact le_on_closure (fun x hx => hb m x (hhost hx)) hclosure continuousOn_const
    (by simpa only [closure_Ioo hcomp.2.1.ne] using hr)

/-- The `k = 1` sine inequality already supplies the travel margin needed
by the interior control construction, with a common exponent. -/
theorem exists_n01aOptical_component_hosts {D : ReferenceData} (hR : RadialReturnMargins D) :
    ∃ A : ℝ, 0 < A ∧ ∀ l h, NegativeRadialComponent D l h →
      ∃ m : ℕ, Ioo l h ⊆ D.cells m ∧
        radialE (D.cellIndex m) ^ (-A) ≤ opticalTravel D.w l h := by
  obtain ⟨A, hA, hmargin⟩ := hR.2
  refine ⟨A, hA, fun l h hcomp => ?_⟩
  obtain ⟨hirr, m, hhost, c, hc, hcinv, hsmall⟩ := hmargin l h hcomp
  refine ⟨m, hhost, ?_⟩
  have hE : 0 < radialE (D.cellIndex m) := exp_pos _
  have hlow : radialE (D.cellIndex m) ^ (-A) ≤ c := by
    rw [rpow_neg hE.le]
    have hinv := one_div_le_one_div_of_le (inv_pos.mpr hc) hcinv
    simpa only [one_div, inv_inv] using hinv
  have hsin : c ≤ |sin (radialTravel D l h)| := by
    simpa only [Nat.cast_one, div_one, one_mul] using hsmall 1 le_rfl
  have htravel : 0 ≤ radialTravel D l h :=
    intervalIntegral.integral_nonneg_of_forall hcomp.2.1.le (fun r => sqrt_nonneg _)
  calc
    radialE (D.cellIndex m) ^ (-A) ≤ c := hlow
    _ ≤ |sin (radialTravel D l h)| := hsin
    _ ≤ |radialTravel D l h| := abs_sin_le_abs
    _ = opticalTravel D.w l h := abs_of_nonneg htravel

/-- The frozen radial-reference assumptions produce quantitative controls
for every supplied family of actual negative components. -/
theorem exists_n01a_opticalControls_of_radialReference {D : ReferenceData}
    (hD : IsRadialReference D) {ι : Type*} {l h : ι → ℝ}
    (hcomp : ∀ i, NegativeRadialComponent D (l i) (h i)) :
    ∃ host : ι → ℕ, ∃ χ : ι → ℝ → ℝ,
      (∀ i, Ioo (l i) (h i) ⊆ D.cells (host i)) ∧
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ Ioo (l i) (h i)) ∧
      (∀ i, HasDerivAt
        (fun t : ℝ => ∫ r in l i..h i,
          sqrt (-deriv (fun x => D.w x * exp (t * χ i x)) r /
            (r * (D.w r * exp (t * χ i r))))) 1 0) ∧
      (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i r,
        |iteratedDeriv s (χ i) r| ≤ B * radialE (D.cellIndex (host i)) ^ B) := by
  classical
  obtain ⟨A, hA, hhosts⟩ := exists_n01aOptical_component_hosts hD.2.2.1
  have hchoose : ∀ i, ∃ m : ℕ, Ioo (l i) (h i) ⊆ D.cells m ∧
      radialE (D.cellIndex m) ^ (-A) ≤ opticalTravel D.w (l i) (h i) :=
    fun i => hhosts (l i) (h i) (hcomp i)
  choose host hhost htravel using hchoose
  obtain ⟨C, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  have hE : ∀ i, 1 ≤ radialE (D.cellIndex (host i)) :=
    fun i => one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hpos : ∀ i r, r ∈ Icc (l i) (h i) → 0 < D.w r := fun i r hr =>
    hgeom.2.2.2.2.1 r ⟨(hcomp i).1.trans_le hr.1, hr.2.trans_lt (hcomp i).2.2.1⟩
  have hjets : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i r, r ∈ Icc (l i) (h i) →
      |iteratedDeriv s (n01aOpticalRadicand D.w) r| ≤ B * radialE (D.cellIndex (host i)) ^ B := by
    intro s
    obtain ⟨B, hB, hb⟩ := n01aOpticalRadicand_component_jets hD.1 s
    exact ⟨B, hB, fun i r hr => hb (l i) (h i) (host i) (hcomp i) (hhost i) r hr⟩
  obtain ⟨χ, hχ, hderiv, hχjets⟩ := exists_n01a_uniform_opticalControls hgeom.1 hgeom.2.1 hA
    (fun i => ⟨(hcomp i).1.le, (hcomp i).2.1, (hcomp i).2.2.1.le⟩)
    hE hgeom.2.2.1.1 hpos (fun i => (hcomp i).2.2.2.2.2)
    (fun i => ⟨(hcomp i).2.2.2.1, (hcomp i).2.2.2.2.1⟩) htravel hjets
  exact ⟨host, χ, hhost, hχ, hderiv, hχjets⟩

end ContinuousFlexibility.Statements
