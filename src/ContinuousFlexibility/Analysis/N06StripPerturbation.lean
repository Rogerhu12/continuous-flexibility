module

public import ContinuousFlexibility.Analysis.CanonicalStripGeometry
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Global inverse for a small perturbation on a strip

A correction with Lipschitz constant at most one half on the closed
unit strip extends by radial clamping with the same constant. Identity
plus this extension is globally bijective, and its inverse is twice
Lipschitz. If the radial correction vanishes at both endpoints, the
bijection preserves the open strip exactly. This supplies a global
inverse criterion for the relative coordinate patch, rather than only
the nonzero endpoint Jacobian.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped NNReal

section Complete

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem n06_halfLipschitz_id_add_antilipschitz {g : E → E}
    (hg : LipschitzWith (1 / 2 : ℝ≥0) g) :
    AntilipschitzWith 2 (fun x => x + g x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := hg.dist_le_mul x y
  have he : x - y = ((x + g x) - (y + g y)) - (g x - g y) := by abel
  have hb : ‖x - y‖ ≤ ‖(x + g x) - (y + g y)‖ + ‖g x - g y‖ := by
    rw [he]
    exact norm_sub_le _ _
  simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h ⊢
  linarith only [h, hb]

/-- The inverse is obtained from an actual contraction on the complete
ambient space. No properness or surjectivity premise is added. -/
theorem n06_halfLipschitz_id_add_bijective {g : E → E}
    (hg : LipschitzWith (1 / 2 : ℝ≥0) g) :
    Function.Bijective (fun x => x + g x) := by
  refine ⟨(n06_halfLipschitz_id_add_antilipschitz hg).injective, ?_⟩
  intro y
  have hcon : ContractingWith (1 / 2 : ℝ≥0) (fun x => y - g x) := by
    refine ⟨by norm_num, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x w
    simpa only [dist_sub_left] using hg.dist_le_mul x w
  let x := ContractingWith.fixedPoint (fun x => y - g x) hcon
  have hx : y - g x = x := hcon.fixedPoint_isFixedPt
  refine ⟨x, ?_⟩
  exact (sub_eq_iff_eq_add.mp hx).symm

theorem n06_halfLipschitz_id_add_inverse {g : E → E}
    (hg : LipschitzWith (1 / 2 : ℝ≥0) g) :
    Function.LeftInverse (Function.invFun (fun x => x + g x)) (fun x => x + g x) ∧
      Function.RightInverse (Function.invFun (fun x => x + g x)) (fun x => x + g x) ∧
      LipschitzWith 2 (Function.invFun (fun x => x + g x)) := by
  have hb := n06_halfLipschitz_id_add_bijective hg
  have hr := Function.rightInverse_invFun hb.surjective
  exact ⟨Function.leftInverse_invFun hb.injective, hr,
    (n06_halfLipschitz_id_add_antilipschitz hg).to_rightInverse hr⟩

end Complete

def n06UnitStripClamp (p : PolarPoint) : PolarPoint :=
  (max 0 (min 1 p.1), p.2)

theorem n06UnitStripClamp_mem (p : PolarPoint) :
    n06UnitStripClamp p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
  exact ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, mem_univ _⟩

theorem n06UnitStripClamp_eq {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    n06UnitStripClamp p = p := by
  simp only [n06UnitStripClamp, min_eq_right hp.2, max_eq_right hp.1, Prod.mk.eta]

theorem n06UnitStripClamp_lipschitz : LipschitzWith 1 n06UnitStripClamp := by
  change LipschitzWith 1 (fun p : ℝ × ℝ => (max 0 (min 1 p.1), p.2))
  simpa only [max_self] using
    ((LipschitzWith.prod_fst.const_min 1).const_max 0).prodMk LipschitzWith.prod_snd

theorem n06_clampedStripCorrection_lipschitz {g : PolarPoint → PolarPoint}
    (hg : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) :
    LipschitzWith (1 / 2 : ℝ≥0) (fun p => g (n06UnitStripClamp p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := (lipschitzOnWith_iff_dist_le_mul.mp hg) _ (n06UnitStripClamp_mem p)
    _ (n06UnitStripClamp_mem q)
  exact h.trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using
      n06UnitStripClamp_lipschitz.dist_le_mul p q) (by positivity))

def n06UnitStripPerturbation (g : PolarPoint → PolarPoint) (p : PolarPoint) : PolarPoint :=
  p + g (n06UnitStripClamp p)

theorem n06UnitStripPerturbation_on_closed {g : PolarPoint → PolarPoint}
    {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    n06UnitStripPerturbation g p = p + g p := by
  rw [n06UnitStripPerturbation, n06UnitStripClamp_eq hp]

/-- The explicit clamped extension is a global bijection with a
Lipschitz inverse, using only the smallness on the original closed strip. -/
theorem n06UnitStripPerturbation_bijective {g : PolarPoint → PolarPoint}
    (hg : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) :
    Function.Bijective (n06UnitStripPerturbation g) ∧
      LipschitzWith 2 (Function.invFun (n06UnitStripPerturbation g)) :=
  ⟨n06_halfLipschitz_id_add_bijective (n06_clampedStripCorrection_lipschitz hg),
    (n06_halfLipschitz_id_add_inverse (n06_clampedStripCorrection_lipschitz hg)).2.2⟩

private theorem n06_strip_radialCorrection_bound {g : PolarPoint → PolarPoint}
    (hg : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    (hzero : ∀ θ, (g (0, θ)).1 = 0 ∧ (g (1, θ)).1 = 0)
    {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    |(g p).1| ≤ (1 / 2 : ℝ) * p.1 ∧
      |(g p).1| ≤ (1 / 2 : ℝ) * (1 - p.1) := by
  have hbound (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hz : (g (r, p.2)).1 = 0) :
      |(g p).1| ≤ (1 / 2 : ℝ) * |p.1 - r| := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hg) p ⟨hp, mem_univ _⟩
      (r, p.2) ⟨hr, mem_univ _⟩
    have hf := LipschitzWith.prod_fst.dist_le_mul (g p) (g (r, p.2))
    simp only [hz, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hf
    have hd : dist p (r, p.2) = |p.1 - r| := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq, sub_self, abs_zero]
      exact max_eq_left (abs_nonneg (p.1 - r))
    rw [hd] at h
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
    exact hf.trans h
  constructor
  · simpa only [sub_zero, abs_of_nonneg hp.1] using
      hbound 0 ⟨le_rfl, zero_le_one⟩ (hzero p.2).1
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hp.2), neg_sub] using
      hbound 1 ⟨zero_le_one, le_rfl⟩ (hzero p.2).2

/-- Vanishing of the radial endpoint correction prevents crossing
either boundary. The angular endpoint values need not be fixed. -/
theorem n06UnitStripPerturbation_mem_open_iff {g : PolarPoint → PolarPoint}
    (hg : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    (hzero : ∀ θ, (g (0, θ)).1 = 0 ∧ (g (1, θ)).1 = 0) (p : PolarPoint) :
    (n06UnitStripPerturbation g p).1 ∈ Ioo (0 : ℝ) 1 ↔ p.1 ∈ Ioo (0 : ℝ) 1 := by
  by_cases hp : p.1 ∈ Ioo (0 : ℝ) 1
  · rw [n06UnitStripPerturbation_on_closed (mem_Icc_of_Ioo hp)]
    have hb := n06_strip_radialCorrection_bound hg hzero (mem_Icc_of_Ioo hp)
    have hglo := neg_abs_le (g p).1
    have hghi := le_abs_self (g p).1
    exact iff_of_true ⟨by change 0 < p.1 + (g p).1; linarith [hb.1, hp.1],
      by change p.1 + (g p).1 < 1; linarith [hb.2, hp.2]⟩ hp
  · have hout : p.1 ≤ 0 ∨ 1 ≤ p.1 := by
      by_cases h0 : p.1 ≤ 0
      · exact Or.inl h0
      · exact Or.inr (le_of_not_gt (fun h1 => hp ⟨lt_of_not_ge h0, h1⟩))
    have he : (n06UnitStripPerturbation g p).1 = p.1 := by
      rcases hout with h0 | h1
      · have hc : n06UnitStripClamp p = (0, p.2) := by
          simp only [n06UnitStripClamp, min_eq_right (h0.trans zero_le_one),
            max_eq_left h0]
        simp only [n06UnitStripPerturbation, hc, Prod.fst_add, (hzero p.2).1, add_zero]
      · have hc : n06UnitStripClamp p = (1, p.2) := by
          simp only [n06UnitStripClamp, min_eq_left h1, max_eq_right zero_le_one]
        simp only [n06UnitStripPerturbation, hc, Prod.fst_add, (hzero p.2).2, add_zero]
    rw [he]

/-- The original perturbation, before clamping, is a bijection of the
open unit strip onto itself. This is the inverse-domain statement needed
for a patched canonical chart. -/
theorem n06_smallStripPerturbation_bijOn {g : PolarPoint → PolarPoint}
    (hg : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    (hzero : ∀ θ, (g (0, θ)).1 = 0 ∧ (g (1, θ)).1 = 0) :
    BijOn (fun p => p + g p) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  have hb := (n06UnitStripPerturbation_bijective hg).1
  have he (p : PolarPoint) (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
      n06UnitStripPerturbation g p = p + g p :=
    n06UnitStripPerturbation_on_closed (mem_Icc_of_Ioo hp.1)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := (n06UnitStripPerturbation_mem_open_iff hg hzero p).mpr hp.1
    rw [he p hp] at h
    exact ⟨h, mem_univ _⟩
  · intro p hp q hq hpq
    exact hb.injective ((he p hp).trans (hpq.trans (he q hq).symm))
  · intro q hq
    obtain ⟨p, hp⟩ := hb.surjective q
    have hp' : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
      ⟨(n06UnitStripPerturbation_mem_open_iff hg hzero p).mp (by rw [hp]; exact hq.1),
        mem_univ _⟩
    exact ⟨p, hp', (he p hp').symm.trans hp⟩

end ContinuousFlexibility.Analysis
