module

public import ContinuousFlexibility.Radial.DeepTailPhysicalJets
public import ContinuousFlexibility.Radial.CentralStatementBridges
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Physical flux coefficients on the actual radial cells

The profile hypotheses already control every ordinary derivative of the
weight and of its reciprocal. A bounded outward index shift preserves
these bounds. The remaining factor `1 / r` has uniformly bounded jets on
the fixed positive radial interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem physical_radialE_one_le (n : ℕ) : 1 ≤ radialE n :=
  one_le_exp_iff.mpr (radialQ_nonneg n)

/-- Values controlled at a physical label at most a fixed number of cells
ahead are coefficient-bounded at the original outward index. -/
theorem physicalCellBound_of_label_bound {cells : ℕ → Set ℝ} {f : ℝ → ℝ}
    (start shift : ℕ) {A : ℝ} (hA : 0 < A)
    (hf : ∀ n x, x ∈ cells n → ∃ m : ℕ, m ≤ start + n + shift ∧
      |f x| ≤ A * radialE m ^ A) :
    PhysicalCellBound cells (fun n => radialE (start + n)) (fun _ => 1) f := by
  obtain ⟨K, hK, hshift⟩ := physicalWeight_shift A hA.le shift
  let C : ℝ := A * K + K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith [mul_pos hA hK]
  have hAKC : A * K ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n x hx => ?_⟩
  obtain ⟨m, hm, hb⟩ := hf n x hx
  have hE : radialE m ≤ radialE (start + n + shift) :=
    exp_le_exp.mpr (radialQ_monotone hm)
  have hw := (rpow_le_rpow (exp_pos _).le hE hA.le).trans (hshift (start + n))
  simp only [mul_one]
  calc
    _ ≤ A * radialE m ^ A := hb
    _ ≤ A * (K * radialE (start + n) ^ K) := mul_le_mul_of_nonneg_left hw hA.le
    _ = (A * K) * radialE (start + n) ^ K := by ring
    _ ≤ C * radialE (start + n) ^ C :=
      mul_le_mul hAKC (rpow_le_rpow_of_exponent_le (physical_radialE_one_le _) hKC)
        (rpow_nonneg (exp_pos _).le _) hC.le

theorem physicalCellBound_of_uniform {cells : ℕ → Set ℝ} {E : ℕ → ℝ}
    (hE : ∀ n, 1 ≤ E n) {f : ℝ → ℝ} {K : ℝ}
    (hf : ∀ n x, x ∈ cells n → |f x| ≤ K) :
    PhysicalCellBound cells E (fun _ => 1) f := by
  let C : ℝ := |K| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun n x hx => ?_⟩
  simp only [mul_one]
  calc
    _ ≤ K := hf n x hx
    _ ≤ C := by dsimp [C]; linarith [le_abs_self K]
    _ ≤ C * E n ^ C := le_mul_of_one_le_right hC.le (one_le_rpow (hE n) hC.le)

section ProfileCoefficients

variable {D : ReferenceData} {cells : ℕ → Set ℝ} {start : ℕ}

/-- The two profile jet estimates remain valid on any outward cells with
the physical label convention of the left or right tail. -/
theorem physical_profile_coefficient_jets (hD : IsAccumulatingProfile D)
    (hlabel : ∀ n r, r ∈ cells n → ∃ m : ℕ,
      r ∈ D.cells m ∧ D.cellIndex m ≤ start + n + 1) :
    (∀ k, PhysicalCellBound cells (fun n => radialE (start + n)) (fun _ => 1)
      (iteratedDeriv k D.w)) ∧
    (∀ k, PhysicalCellBound cells (fun n => radialE (start + n)) (fun _ => 1)
      (iteratedDeriv k (fun r => (D.w r)⁻¹))) := by
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hfinite, hlocal, hdist,
    hlower, hwjets, hinvjets, hwidth, habsorb, htrace⟩ := hD
  constructor
  · intro k
    apply physicalCellBound_of_label_bound start 1 (hC k)
    intro n r hr
    obtain ⟨m, hm, hi⟩ := hlabel n r hr
    refine ⟨D.cellIndex m, hi, ?_⟩
    have hj : |iteratedDeriv k D.w r| ≤ C k *
        exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C k * (D.cellIndex m : ℝ) ^ 2) := by
      simpa only [radialJet_eq_iteratedDeriv] using hwjets m r hm k
    apply hj.trans
    apply mul_le_mul_of_nonneg_left _ (hC k).le
    rw [radialE, ← exp_mul]
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q (D.cellIndex m)) (hC k).le
    have hp : 0 ≤ (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  · intro k
    apply physicalCellBound_of_label_bound start 1 (hC k)
    intro n r hr
    obtain ⟨m, hm, hi⟩ := hlabel n r hr
    refine ⟨D.cellIndex m, hi, ?_⟩
    simpa only [radialJet_eq_iteratedDeriv] using hinvjets m r hm k

/-- The inverse radius has a uniform bound for every ordinary derivative
on the entire positive closed radial interval. -/
theorem physical_inverseRadius_jets {a b : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ K : ℝ, ∀ r ∈ Icc a b, |iteratedDeriv k (fun x : ℝ => x⁻¹) r| ≤ K := by
  have hc : ContinuousOn (iteratedDeriv k (fun x : ℝ => x⁻¹)) (Icc a b) := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv']
    exact continuousOn_const.mul
      (continuousOn_id.zpow₀ (-1 - (k : ℤ))
        (fun r hr => Or.inl (ne_of_gt (ha.trans_le hr.1))))
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  exact ⟨K, fun r hr => by simpa only [Real.norm_eq_abs] using hK r hr⟩

/-- The reciprocal weight and the source coefficient in the physical
flux system have coefficient bounds of every actual derivative order. -/
theorem physical_flux_coefficient_jets (hD : IsAccumulatingProfile D)
    (hlabel : ∀ n r, r ∈ cells n → ∃ m : ℕ,
      r ∈ D.cells m ∧ D.cellIndex m ≤ start + n + 1) (a : ℝ) :
    (∀ k, PhysicalCellBound cells (fun n => radialE (start + n)) (fun _ => 1)
      (iteratedDeriv k (fun r => (D.w r)⁻¹))) ∧
    (∀ k, PhysicalCellBound cells (fun n => radialE (start + n)) (fun _ => 1)
      (iteratedDeriv k (fun r => a * (deriv D.w r * r⁻¹)))) := by
  have hprofile := physical_profile_coefficient_jets hD hlabel
  obtain ⟨C, hb⟩ := hD
  have hcore : ∀ n r, r ∈ cells n → r ∈ radialCore D := by
    intro n r hr
    obtain ⟨m, hm, hi⟩ := hlabel n r hr
    exact hb.2.1.2.2.2.1 m hm
  have hw : ContDiff ℝ ∞ D.w := hb.1.2.2.1.1
  have hw' : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hpos : 0 < D.a := hb.1.1
  have hE : ∀ n, 1 ≤ radialE (start + n) := fun n => physical_radialE_one_le _
  have hOne : ∀ n : ℕ, 0 ≤ (1 : ℝ) := fun _ => zero_le_one
  have hrecip (k : ℕ) : PhysicalCellBound cells (fun n => radialE (start + n))
      (fun _ => 1) (iteratedDeriv k (fun r : ℝ => r⁻¹)) := by
    obtain ⟨K, hK⟩ := physical_inverseRadius_jets (b := D.b) hpos k
    exact physicalCellBound_of_uniform hE
      (fun n r hr => hK r ⟨(hcore n r hr).1.le, (hcore n r hr).2.le⟩)
  refine ⟨hprofile.2, fun k => ?_⟩
  have hprod := physicalCellBound_iteratedDeriv_mul hE hOne k
    (fun n r hr => hw'.contDiffAt)
    (fun n r hr => contDiffAt_id.inv (ne_of_gt (hpos.trans (hcore n r hr).1)))
    (fun i hi => by simpa only [← iteratedDeriv_succ'] using hprofile.1 (i + 1))
    (fun i hi => hrecip i)
  apply (hprod.const_mul hE hOne a).congr
  intro n r hr
  exact (iteratedDeriv_const_mul_field a (fun r => deriv D.w r * r⁻¹)).symm

end ProfileCoefficients

end ContinuousFlexibility.Radial
