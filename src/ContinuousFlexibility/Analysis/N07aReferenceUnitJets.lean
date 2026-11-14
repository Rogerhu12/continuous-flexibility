module

public import ContinuousFlexibility.Statements.N07aCanonicalGeometry
public import ContinuousFlexibility.Analysis.N07aIntervalOpenEnergy

/-!
# The actual reference coefficients in unit radial coordinates

These functions are restrictions of the primitive geometric atoms. The
potential and angular principal coefficient acquire the square interval
length when the reference equation is written on the unit interval.
The quotient uses the already controlled actual inverse-leading atom.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

def n07aReferenceUnitAtom (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (m : ℕ) (a : Atom) (r : ℝ) : ℝ :=
  atom D T S C L K (C.referenceState, 0) m a (r, 0)

def n07aReferenceUnitC (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (m : ℕ) (r : ℝ) : ℝ :=
  (K.right m - K.left m) ^ 2 * n07aReferenceUnitAtom D T S C L K m .principalC r

def n07aReferenceUnitV (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (m : ℕ) (r : ℝ) : ℝ :=
  (K.right m - K.left m) ^ 2 * n07aReferenceUnitAtom D T S C L K m .potential r

def n07aReferenceUnitQ (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (m : ℕ) (r : ℝ) : ℝ :=
  (K.right m - K.left m) ^ 2 *
    (n07aReferenceUnitAtom D T S C L K m .principalC r *
      n07aReferenceUnitAtom D T S C L K m .principalAInverse r)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07aReferenceUnitAtom_contDiff
    (hJ : ReferenceJets D T S C L K) (m : ℕ) (a : Atom) :
    ContDiffOn ℝ ∞ (n07aReferenceUnitAtom D T S C L K m a) (Ioo (0 : ℝ) 1) :=
  (hJ.1 m a).1.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun _ hx => ⟨hx, mem_univ _⟩)

theorem n07aReferenceUnitAtom_iteratedDeriv (m : ℕ) (a : Atom) (k : ℕ) (r : ℝ) :
    iteratedDeriv k (n07aReferenceUnitAtom D T S C L K m a) r =
      mixedDerivative k 0 (atom D T S C L K (C.referenceState, 0) m a) (r, 0) := by
  unfold n07aReferenceUnitAtom
  simp only [mixedDerivative, iteratedDeriv_zero]

/-- The actual primitive two-jet bound, restricted to the same unit ray. -/
theorem n07aReferenceUnitAtom_twoJet_bound (hJ : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m a r, r ∈ Ioo (0 : ℝ) 1 → ∀ k : ℕ, k ≤ 2 →
      |iteratedDeriv k (n07aReferenceUnitAtom D T S C L K m a) r| ≤
        A * T.E0 (T.sample (K.cell m)) ^ A := by
  obtain ⟨A, hA, hb⟩ := hJ.2 2
  refine ⟨A, hA, ?_⟩
  intro m a r hr k hk
  rw [n07aReferenceUnitAtom_iteratedDeriv]
  exact hb m a (r, 0) ⟨hr, mem_univ _⟩ k 0 (by simpa only [Nat.add_zero] using hk)

theorem n07aReferenceUnit_scaled_contDiff (hJ : ReferenceJets D T S C L K) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07aReferenceUnitC D T S C L K m) (Ioo (0 : ℝ) 1) ∧
    ContDiffOn ℝ ∞ (n07aReferenceUnitV D T S C L K m) (Ioo (0 : ℝ) 1) ∧
    ContDiffOn ℝ ∞ (n07aReferenceUnitQ D T S C L K m) (Ioo (0 : ℝ) 1) := by
  exact ⟨contDiffOn_const.mul (n07aReferenceUnitAtom_contDiff hJ m .principalC),
    contDiffOn_const.mul (n07aReferenceUnitAtom_contDiff hJ m .potential),
    contDiffOn_const.mul ((n07aReferenceUnitAtom_contDiff hJ m .principalC).mul
      (n07aReferenceUnitAtom_contDiff hJ m .principalAInverse))⟩

theorem n07aReferenceUnitAtom_inverse (m : ℕ) (r : ℝ) :
    n07aReferenceUnitAtom D T S C L K m .principalAInverse r =
      (n07aReferenceUnitAtom D T S C L K m .principalA r)⁻¹ := by
  simp only [n07aReferenceUnitAtom, atom]

theorem n07aReferenceUnitQ_eq_div (m : ℕ) (r : ℝ) :
    n07aReferenceUnitQ D T S C L K m r =
      n07aReferenceUnitC D T S C L K m r /
        n07aReferenceUnitAtom D T S C L K m .principalA r := by
  rw [n07aReferenceUnitQ, n07aReferenceUnitC, n07aReferenceUnitAtom_inverse]
  ring

theorem n07a_canonicalUnitPoint_mem (m : ℕ) (hlen : K.left m < K.right m)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    canonicalUnitPoint K m (r, 0) ∈ canonicalOpen S K m := by
  have hl : 0 < (K.right m - K.left m) * r := mul_pos (sub_pos.mpr hlen) hr.1
  have hu : (K.right m - K.left m) * r < K.right m - K.left m :=
    mul_lt_of_lt_one_right (sub_pos.mpr hlen) hr.2
  refine ⟨?_, mem_univ _⟩
  dsimp only [canonicalUnitPoint]
  constructor <;> linarith

theorem n07aReferenceUnitAtom_A_pos (hP : ReferencePrincipal T S C K)
    (m : ℕ) (hlen : K.left m < K.right m) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < n07aReferenceUnitAtom D T S C L K m .principalA r :=
  (hP.1 m (canonicalUnitPoint K m (r, 0)) (n07a_canonicalUnitPoint_mem m hlen hr)).1

theorem n07aReferenceUnitC_eq_A_mul_Q (hP : ReferencePrincipal T S C K)
    (m : ℕ) (hlen : K.left m < K.right m) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    n07aReferenceUnitC D T S C L K m r =
      n07aReferenceUnitAtom D T S C L K m .principalA r *
        n07aReferenceUnitQ D T S C L K m r := by
  rw [n07aReferenceUnitQ_eq_div]
  field_simp [(n07aReferenceUnitAtom_A_pos (D := D) (L := L) hP m hlen hr).ne']

end ContinuousFlexibility.Analysis
