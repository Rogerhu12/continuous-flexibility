module

public import ContinuousFlexibility.Radial.MorseWeakEnergy
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The graph associated with the actual Morse form

The associated graph is defined by the physical weak-energy form. A genuine
Lax--Milgram inverse gives its shifted resolvent, closedness and maximal graph
adjoint property. No compact form-core identification, Friedrichs claim, or
classification of the Morse spectrum is made here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

local instance : SeminormedAddCommGroup (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance : NormedSpace ℝ (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem morseShiftedForm_symm (α w V : ℝ) (u v : MorseWeakEnergy) :
    morseShiftedForm α w V u v = morseShiftedForm α w V v u := by
  rw [morseShiftedForm_apply, morseShiftedForm_apply, morsePhysicalForm_symm,
    real_inner_comm (morseEnergyBase v) (morseEnergyBase u)]

/-- The actual Riesz representative of the coercive form is an equivalence. -/
def morseLaxMilgramEquiv (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    MorseWeakEnergy ≃L[ℝ] MorseWeakEnergy :=
  (morseShiftedForm_isCoercive α V hw).continuousLinearEquivOfBilin

theorem morseLaxMilgramEquiv_inner (α V : ℝ) {w : ℝ} (hw : 0 < w)
    (u v : MorseWeakEnergy) :
    ⟪morseLaxMilgramEquiv α V hw u, v⟫_ℝ = morseShiftedForm α w V u v :=
  (morseShiftedForm_isCoercive α V hw).continuousLinearEquivOfBilin_apply u v

/-- Solve the variational equation in the complete physical energy space. -/
def morseEnergyResolvent (α V : ℝ) {w : ℝ} (hw : 0 < w) : MorseL2 →L[ℝ] MorseWeakEnergy :=
  (morseLaxMilgramEquiv α V hw).symm.toContinuousLinearMap.comp morseEnergyBase.adjoint

theorem morseEnergyResolvent_spec (α V : ℝ) {w : ℝ} (hw : 0 < w)
    (f : MorseL2) (v : MorseWeakEnergy) :
    morseShiftedForm α w V (morseEnergyResolvent α V hw f) v =
      ⟪f, morseEnergyBase v⟫_ℝ := by
  calc
    _ = ⟪morseLaxMilgramEquiv α V hw (morseEnergyResolvent α V hw f), v⟫_ℝ :=
      (morseLaxMilgramEquiv_inner α V hw _ _).symm
    _ = ⟪morseEnergyBase.adjoint f, v⟫_ℝ := by
      change ⟪morseLaxMilgramEquiv α V hw
        ((morseLaxMilgramEquiv α V hw).symm (morseEnergyBase.adjoint f)), v⟫_ℝ = _
      rw [ContinuousLinearEquiv.apply_symm_apply]
    _ = _ := morseEnergyBase.adjoint_inner_left v f

theorem morseEnergyResolvent_unique (α V : ℝ) {w : ℝ} (hw : 0 < w)
    (f : MorseL2) (u : MorseWeakEnergy)
    (hu : ∀ v, morseShiftedForm α w V u v = ⟪f, morseEnergyBase v⟫_ℝ) :
    u = morseEnergyResolvent α V hw f := by
  apply (morseLaxMilgramEquiv α V hw).injective
  apply ext_inner_right ℝ
  intro v
  rw [morseLaxMilgramEquiv_inner, morseLaxMilgramEquiv_inner,
    hu v, morseEnergyResolvent_spec]

def morseShiftedResolvent (α V : ℝ) {w : ℝ} (hw : 0 < w) : MorseL2 →L[ℝ] MorseL2 :=
  morseEnergyBase.comp (morseEnergyResolvent α V hw)

@[simp] theorem morseShiftedResolvent_apply (α V : ℝ) {w : ℝ} (hw : 0 < w) (f : MorseL2) :
    morseShiftedResolvent α V hw f = morseEnergyBase (morseEnergyResolvent α V hw f) := rfl

theorem morseEnergyResolvent_norm_bound (α V : ℝ) {w : ℝ} (hw : 0 < w) (f : MorseL2) :
    ‖morseEnergyResolvent α V hw f‖ ≤ (morseCoercivityConstant w)⁻¹ * ‖f‖ := by
  have hc := morseCoercivityConstant_pos hw
  have hco := morseShiftedForm_coercive_bound α w V (morseEnergyResolvent α V hw f)
  rw [morseEnergyResolvent_spec] at hco
  have hb : morseCoercivityConstant w * ‖morseEnergyResolvent α V hw f‖ ^ 2 ≤
      ‖f‖ * ‖morseEnergyResolvent α V hw f‖ :=
    hco.trans ((real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (morseEnergyCoordinate_norm_le 0 _) (norm_nonneg f)))
  by_cases hz : ‖morseEnergyResolvent α V hw f‖ = 0
  · rw [hz]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg f)
  · have hp : 0 < ‖morseEnergyResolvent α V hw f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hcu : morseCoercivityConstant w * ‖morseEnergyResolvent α V hw f‖ ≤ ‖f‖ :=
      (mul_le_mul_iff_left₀ hp).mp (by nlinarith [hb])
    have hd : ‖morseEnergyResolvent α V hw f‖ ≤ ‖f‖ / morseCoercivityConstant w :=
      (le_div_iff₀ hc).mpr (by nlinarith [hcu])
    simpa only [div_eq_mul_inv, mul_comm] using hd

theorem morseShiftedResolvent_norm_bound (α V : ℝ) {w : ℝ} (hw : 0 < w) (f : MorseL2) :
    ‖morseShiftedResolvent α V hw f‖ ≤ (morseCoercivityConstant w)⁻¹ * ‖f‖ :=
  (morseEnergyCoordinate_norm_le 0 _).trans (morseEnergyResolvent_norm_bound α V hw f)

theorem morseShiftedResolvent_injective (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    Function.Injective (morseShiftedResolvent α V hw) := by
  intro f g hfg
  have he : morseEnergyResolvent α V hw f = morseEnergyResolvent α V hw g :=
    morseEnergyBase_injective hfg
  apply morseEnergyBase_denseRange.eq_of_inner_left ℝ
  intro v
  have hf := morseEnergyResolvent_spec α V hw f v
  have hg := morseEnergyResolvent_spec α V hw g v
  rw [he] at hf
  exact hf.symm.trans hg

theorem morseShiftedResolvent_pairing (α V : ℝ) {w : ℝ} (hw : 0 < w) (f g : MorseL2) :
    ⟪morseShiftedResolvent α V hw f, g⟫_ℝ =
      ⟪f, morseShiftedResolvent α V hw g⟫_ℝ := by
  calc
    _ = ⟪g, morseEnergyBase (morseEnergyResolvent α V hw f)⟫_ℝ := real_inner_comm _ _
    _ = morseShiftedForm α w V (morseEnergyResolvent α V hw g)
        (morseEnergyResolvent α V hw f) := (morseEnergyResolvent_spec α V hw g _).symm
    _ = morseShiftedForm α w V (morseEnergyResolvent α V hw f)
        (morseEnergyResolvent α V hw g) := morseShiftedForm_symm _ _ _ _ _
    _ = _ := morseEnergyResolvent_spec α V hw f _

theorem morseShiftedResolvent_denseRange (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    DenseRange (morseShiftedResolvent α V hw) := by
  let R := morseShiftedResolvent α V hw
  have horth : R.rangeᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    rw [Submodule.mem_bot]
    have hh := (Submodule.mem_orthogonal R.range u).mp hu (R (R u)) ⟨R u, rfl⟩
    change ⟪morseShiftedResolvent α V hw (R u), u⟫_ℝ = 0 at hh
    rw [morseShiftedResolvent_pairing] at hh
    have hRu : R u = 0 := inner_self_eq_zero.mp hh
    apply morseShiftedResolvent_injective α V hw
    rw [hRu, map_zero]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (R.range.topologicalClosure_eq_top_iff.mpr horth)

/-- The actual form-associated graph; closedness is proved below. -/
def morseAssociatedGraph (α w V : ℝ) : Submodule ℝ (MorseL2 × MorseL2) where
  carrier := {p | ∃ u : MorseWeakEnergy, morseEnergyBase u = p.1 ∧
    ∀ v : MorseWeakEnergy, morsePhysicalForm α w V u v = ⟪p.2, morseEnergyBase v⟫_ℝ}
  zero_mem' := ⟨0, by simp, by intros; simp⟩
  add_mem' := by
    rintro p q ⟨u, hu, hqu⟩ ⟨v, hv, hqv⟩
    refine ⟨u + v, ?_, ?_⟩
    · change morseEnergyBase (u + v) = p.1 + q.1
      rw [map_add, hu, hv]
    · intro z
      change morsePhysicalForm α w V (u + v) z = ⟪p.2 + q.2, morseEnergyBase z⟫_ℝ
      rw [map_add]
      change morsePhysicalForm α w V u z + morsePhysicalForm α w V v z = _
      rw [inner_add_left, hqu z, hqv z]
  smul_mem' := by
    rintro a p ⟨u, hu, hqu⟩
    refine ⟨a • u, ?_, ?_⟩
    · change morseEnergyBase (a • u) = a • p.1
      rw [map_smul, hu]
    · intro z
      change morsePhysicalForm α w V (a • u) z = ⟪a • p.2, morseEnergyBase z⟫_ℝ
      rw [map_smul]
      change a * morsePhysicalForm α w V u z = _
      rw [real_inner_smul_left, hqu z]

theorem mem_morseAssociatedGraph_shift_iff (α w V : ℝ) (u f : MorseL2) :
    (u, f) ∈ morseAssociatedGraph α w V ↔
      ∃ z : MorseWeakEnergy, morseEnergyBase z = u ∧ ∀ v : MorseWeakEnergy,
        morseShiftedForm α w V z v =
          ⟪f + morseFormShift α V • u, morseEnergyBase v⟫_ℝ := by
  constructor
  · rintro ⟨z, hz, hq⟩
    refine ⟨z, hz, ?_⟩
    intro v
    rw [morseShiftedForm_apply, hq v, hz, inner_add_left, real_inner_smul_left]
  · rintro ⟨z, hz, hq⟩
    refine ⟨z, hz, ?_⟩
    intro v
    have hh := hq v
    rw [morseShiftedForm_apply, hz, inner_add_left, real_inner_smul_left] at hh
    linarith

/-- Identification with a genuine bounded resolvent proves graph properties. -/
theorem mem_morseAssociatedGraph_iff_resolvent (α V : ℝ) {w : ℝ} (hw : 0 < w)
    (u f : MorseL2) :
    (u, f) ∈ morseAssociatedGraph α w V ↔
      u = morseShiftedResolvent α V hw (f + morseFormShift α V • u) := by
  rw [mem_morseAssociatedGraph_shift_iff]
  constructor
  · rintro ⟨z, hz, hq⟩
    have he := morseEnergyResolvent_unique α V hw _ z hq
    calc
      u = morseEnergyBase z := hz.symm
      _ = morseEnergyBase (morseEnergyResolvent α V hw (f + morseFormShift α V • u)) :=
        congrArg morseEnergyBase he
      _ = _ := rfl
  · intro hu
    refine ⟨morseEnergyResolvent α V hw (f + morseFormShift α V • u), hu.symm, ?_⟩
    intro v
    exact morseEnergyResolvent_spec α V hw _ v

theorem morseShiftedResolvent_mem_graph (α V : ℝ) {w : ℝ} (hw : 0 < w) (f : MorseL2) :
    (morseShiftedResolvent α V hw f,
      f - morseFormShift α V • morseShiftedResolvent α V hw f) ∈ morseAssociatedGraph α w V := by
  rw [mem_morseAssociatedGraph_iff_resolvent α V hw, sub_add_cancel]

theorem morseAssociatedGraph_isClosed (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    IsClosed (morseAssociatedGraph α w V : Set (MorseL2 × MorseL2)) := by
  have heq : (morseAssociatedGraph α w V : Set (MorseL2 × MorseL2)) =
      {p | p.1 = morseShiftedResolvent α V hw (p.2 + morseFormShift α V • p.1)} := by
    ext p
    exact mem_morseAssociatedGraph_iff_resolvent α V hw p.1 p.2
  rw [heq]
  exact isClosed_eq continuous_fst
    ((morseShiftedResolvent α V hw).continuous.comp
      (continuous_snd.add (continuous_fst.const_smul (morseFormShift α V))))

theorem morseAssociatedGraph_domain_iff (α V : ℝ) {w : ℝ} (hw : 0 < w) (u : MorseL2) :
    (∃ f, (u, f) ∈ morseAssociatedGraph α w V) ↔
      ∃ g, morseShiftedResolvent α V hw g = u := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f + morseFormShift α V • u,
      ((mem_morseAssociatedGraph_iff_resolvent α V hw u f).mp hf).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, morseShiftedResolvent_mem_graph α V hw g⟩

theorem morseAssociatedGraph_domain_dense (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    Dense {u : MorseL2 | ∃ f, (u, f) ∈ morseAssociatedGraph α w V} := by
  have heq : {u : MorseL2 | ∃ f, (u, f) ∈ morseAssociatedGraph α w V} =
      Set.range (morseShiftedResolvent α V hw) := by
    ext u
    exact morseAssociatedGraph_domain_iff α V hw u
  rw [heq]
  exact morseShiftedResolvent_denseRange α V hw

theorem morseAssociatedGraph_unique (α w V : ℝ) (u f g : MorseL2)
    (hf : (u, f) ∈ morseAssociatedGraph α w V)
    (hg : (u, g) ∈ morseAssociatedGraph α w V) : f = g := by
  rcases hf with ⟨z, hz, hqz⟩
  rcases hg with ⟨y, hy, hqy⟩
  have he : z = y := morseEnergyBase_injective (hz.trans hy.symm)
  subst y
  apply morseEnergyBase_denseRange.eq_of_inner_left ℝ
  intro v
  exact (hqz v).symm.trans (hqy v)

theorem morseAssociatedGraph_semibounded (α V : ℝ) {w : ℝ} (hw : 0 < w)
    (u f : MorseL2) (h : (u, f) ∈ morseAssociatedGraph α w V) :
    -(morseFormShift α V * ‖u‖ ^ 2) ≤ ⟪f, u⟫_ℝ := by
  rcases h with ⟨z, hz, hq⟩
  have hb := morseShiftedForm_coercive_bound α w V z
  rw [morseShiftedForm_apply, hq z, hz, real_inner_self_eq_norm_sq] at hb
  have hn := mul_nonneg (morseCoercivityConstant_pos hw).le (sq_nonneg ‖z‖)
  linarith

theorem morseAssociatedGraph_symmetric (α w V : ℝ) (p q : MorseL2 × MorseL2)
    (hp : p ∈ morseAssociatedGraph α w V) (hq : q ∈ morseAssociatedGraph α w V) :
    ⟪p.2, q.1⟫_ℝ = ⟪p.1, q.2⟫_ℝ := by
  rcases hp with ⟨u, hu, hpu⟩
  rcases hq with ⟨v, hv, hqv⟩
  calc
    _ = morsePhysicalForm α w V u v := by rw [← hv]; exact (hpu v).symm
    _ = morsePhysicalForm α w V v u := morsePhysicalForm_symm _ _ _ _ _
    _ = ⟪q.2, p.1⟫_ℝ := by rw [← hu]; exact hqv u
    _ = _ := real_inner_comm _ _

/-- The usual Hilbert graph-adjoint relation, with both pairings in `L²(dX)`. -/
def morseAssociatedAdjointGraph (α w V : ℝ) : Submodule ℝ (MorseL2 × MorseL2) where
  carrier := {p | ∀ q ∈ morseAssociatedGraph α w V, ⟪p.2, q.1⟫_ℝ = ⟪p.1, q.2⟫_ℝ}
  zero_mem' := by simp
  add_mem' := by
    intro p r hp hr q hq
    change ⟪p.2 + r.2, q.1⟫_ℝ = ⟪p.1 + r.1, q.2⟫_ℝ
    rw [inner_add_left, inner_add_left, hp q hq, hr q hq]
  smul_mem' := by
    intro a p hp q hq
    change ⟪a • p.2, q.1⟫_ℝ = ⟪a • p.1, q.2⟫_ℝ
    rw [real_inner_smul_left, real_inner_smul_left, hp q hq]

theorem morseAssociatedGraph_eq_adjoint (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    morseAssociatedGraph α w V = morseAssociatedAdjointGraph α w V := by
  apply le_antisymm
  · intro p hp q hq
    exact morseAssociatedGraph_symmetric α w V p q hp hq
  · intro p hp
    apply (mem_morseAssociatedGraph_iff_resolvent α V hw p.1 p.2).mpr
    apply ext_inner_right ℝ
    intro g
    have hh := hp _ (morseShiftedResolvent_mem_graph α V hw g)
    change ⟪p.2, morseShiftedResolvent α V hw g⟫_ℝ =
      ⟪p.1, g - morseFormShift α V • morseShiftedResolvent α V hw g⟫_ℝ at hh
    rw [inner_sub_right, real_inner_smul_right] at hh
    have hr := morseShiftedResolvent_pairing α V hw (p.2 + morseFormShift α V • p.1) g
    rw [inner_add_left, real_inner_smul_left] at hr
    linarith

theorem morseL2_inner_right_toLp (u : MorseL2) {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    ⟪u, hφ.toLp φ⟫_ℝ = ∫ x : ℝ, u x * φ x := by
  calc
    _ = ⟪hφ.toLp φ, u⟫_ℝ := real_inner_comm _ _
    _ = _ := morseTestPairing_apply φ hφ u

theorem morseCompactImage_memLp {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (α w V : ℝ) :
    MemLp (morseExpression α w V φ) 2 volume := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hp : ContDiff ℝ ∞ (fun x : ℝ =>
      w ^ 2 * exp (-x) ^ 2 - w * (2 * α + 1) * exp (-x) + V) :=
    ((contDiff_const.mul (contDiff_id.neg.exp.pow 2)).sub
      (contDiff_const.mul contDiff_id.neg.exp)).add contDiff_const
  have hH : ContDiff ℝ ∞ (morseExpression α w V φ) := hdd.neg.add (hp.mul hφ)
  have hcH : HasCompactSupport (morseExpression α w V φ) :=
    hc.deriv.deriv.neg.add (hc.mul_left (f := fun x : ℝ =>
      w ^ 2 * exp (-x) ^ 2 - w * (2 * α + 1) * exp (-x) + V))
  exact hH.continuous.memLp_of_hasCompactSupport hcH

/-- Move the actual weak derivative onto a compact test. The exponential
multiplier is replaced by its proved almost-everywhere physical value. -/
theorem morsePhysicalForm_weak_test (u : MorseWeakEnergy) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (α w V : ℝ) :
    morsePhysicalForm α w V u (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) =
      ∫ x : ℝ, morseEnergyBase u x * morseExpression α w V φ x := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  let ht := compactSmooth_morseEnergyDomain hφ hc
  have hφdd : MemLp (deriv (deriv φ)) 2 volume :=
    hdd.continuous.memLp_of_hasCompactSupport hc.deriv.deriv
  have hφww : MemLp (fun x : ℝ => exp (-x) ^ 2 * φ x) 2 volume :=
    ((continuous_id.neg.rexp.pow 2).mul hφ.continuous).memLp_of_hasCompactSupport hc.mul_left
  have hI := morseEnergyDerivative_weak u (deriv φ) hd hc.deriv
  have hW : (∫ x : ℝ, morseEnergyWeight u x * φ x) =
      ∫ x : ℝ, morseEnergyBase u x * (exp (-x) * φ x) := by
    apply integral_congr_ae
    filter_upwards [morseEnergyWeight_ae u] with x hx
    rw [hx]
    ring
  have hWW : (∫ x : ℝ, morseEnergyWeight u x * (exp (-x) * φ x)) =
      ∫ x : ℝ, morseEnergyBase u x * (exp (-x) ^ 2 * φ x) := by
    apply integral_congr_ae
    filter_upwards [morseEnergyWeight_ae u] with x hx
    rw [hx]
    ring
  have hiD := (Lp.memLp (morseEnergyBase u)).integrable_mul hφdd
  have hiWW := (Lp.memLp (morseEnergyBase u)).integrable_mul hφww
  have hiW := (Lp.memLp (morseEnergyBase u)).integrable_mul ht.2.2.2
  have hi0 := (Lp.memLp (morseEnergyBase u)).integrable_mul ht.2.1
  have hs := integral_add ((hiD.neg.add (hiWW.const_mul (w ^ 2))).sub
    (hiW.const_mul (w * (2 * α + 1)))) (hi0.const_mul V)
  have hm := integral_sub (hiD.neg.add (hiWW.const_mul (w ^ 2)))
    (hiW.const_mul (w * (2 * α + 1)))
  have ha := integral_add hiD.neg (hiWW.const_mul (w ^ 2))
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hs hm ha
  have hR : (∫ x : ℝ, morseEnergyBase u x * morseExpression α w V φ x) =
      -(∫ x : ℝ, morseEnergyBase u x * deriv (deriv φ) x) +
      w ^ 2 * (∫ x : ℝ, morseEnergyBase u x * (exp (-x) ^ 2 * φ x)) -
      w * (2 * α + 1) * (∫ x : ℝ, morseEnergyBase u x * (exp (-x) * φ x)) +
      V * (∫ x : ℝ, morseEnergyBase u x * φ x) := by
    calc
      _ = ∫ x : ℝ, -(morseEnergyBase u x * deriv (deriv φ) x) +
          w ^ 2 * (morseEnergyBase u x * (exp (-x) ^ 2 * φ x)) -
          w * (2 * α + 1) * (morseEnergyBase u x * (exp (-x) * φ x)) +
          V * (morseEnergyBase u x * φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        unfold morseExpression
        ring
      _ = _ := by
        rw [hs, hm, ha, integral_neg]
        simp only [integral_const_mul]
  rw [morsePhysicalForm_apply]
  simp only [morseEnergyLift_base, morseEnergyLift_derivative, morseEnergyLift_weight,
    morseL2_inner_right_toLp]
  rw [hI, hWW, hW]
  exact hR.symm

/-- The associated graph contains the genuine differential image of each
smooth compact function. This is inclusion, not an operator-core theorem. -/
theorem morseCompact_pair_mem_graph {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (α w V : ℝ) :
    ((compactSmooth_morseEnergyDomain hφ hc).2.1.toLp φ,
      (morseCompactImage_memLp hφ hc α w V).toLp (morseExpression α w V φ)) ∈
        morseAssociatedGraph α w V := by
  refine ⟨morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc), rfl, ?_⟩
  intro u
  calc
    _ = morsePhysicalForm α w V u
        (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) :=
      morsePhysicalForm_symm _ _ _ _ _
    _ = ∫ x : ℝ, morseEnergyBase u x * morseExpression α w V φ x :=
      morsePhysicalForm_weak_test u hφ hc α w V
    _ = _ := (morseTestPairing_apply _ (morseCompactImage_memLp hφ hc α w V) _).symm

/-- The distributional equation is an output of the variational graph.
The converse requires a separately proved form-core approximation theorem. -/
def MorseCompactWeakEquation (α w V : ℝ) (u f : MorseL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, f x * φ x) = ∫ x : ℝ, u x * morseExpression α w V φ x

theorem morseAssociatedGraph_compact_weak (α w V : ℝ) (u f : MorseL2)
    (h : (u, f) ∈ morseAssociatedGraph α w V) : MorseCompactWeakEquation α w V u f := by
  rcases h with ⟨z, hz, hq⟩
  change morseEnergyBase z = u at hz
  intro φ hφ hc
  have hh := hq (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc))
  rw [morsePhysicalForm_weak_test z hφ hc α w V,
    morseEnergyLift_base, morseL2_inner_right_toLp] at hh
  rw [← hz]
  exact hh.symm

end ContinuousFlexibility.Radial
