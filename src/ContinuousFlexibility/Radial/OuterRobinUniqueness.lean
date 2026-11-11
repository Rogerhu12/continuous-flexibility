import ContinuousFlexibility.Radial.OuterFundamentalKernel
import ContinuousFlexibility.Radial.OuterFirstOrderRegularity

/-!
# Robin uniqueness with a genuine one-sided entrance state

The differential system is required only in the open interval.  Continuity
extends its constant state determinant to the entrance.  Thus uniqueness
does not assume an ordinary derivative across that boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

theorem outerFirstOrderSystem_determinant_Ico
    {a b : ℝ} {alpha beta u z v q : ℝ → ℝ} (hab : a < b)
    (hu : ContinuousOn u (Ico a b)) (hz : ContinuousOn z (Ico a b))
    (hv : ContinuousOn v (Ico a b)) (hq : ContinuousOn q (Ico a b))
    (hU : OuterFirstOrderSystem alpha beta u z (Ioo a b))
    (hV : OuterFirstOrderSystem alpha beta v q (Ioo a b)) :
    ∀ x ∈ Ico a b, u x * q x - z x * v x = u a * q a - z a * v a := by
  obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hab
  have hconst : EqOn (fun x => u x * q x - z x * v x)
      (fun _ => u d * q d - z d * v d) (Ioo a b) :=
    fun x hx => outerFirstOrderSystem_state_determinant (convex_Ioo a b) hU hV hd hx
  have hclosure : Ico a b ⊆ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  have hall := hconst.of_subset_closure ((hu.mul hq).sub (hz.mul hv))
    continuousOn_const Ioo_subset_Ico_self hclosure
  intro x hx
  exact (hall hx).trans (hall ⟨le_rfl, hab⟩).symm

theorem OuterFundamentalStatePair.robin_unique_continuous_state
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b)
    (hα : ∀ x ∈ Ioo c b, alpha x ≠ 0)
    {u z : ℝ → ℝ} (hu : ContinuousOn u (Ico a b))
    (hz : ContinuousOn z (Ico a b))
    (hstate : OuterFirstOrderSystem alpha beta u z (Ioo a b))
    (hRobin : outerStatePair H.entrance (u a, z a) = 0)
    (hnatural : ∃ C : ℝ, ∀ x ∈ Ioo c b, u x = C * P x) :
    ∀ x ∈ Ico a b, u x = 0 ∧ z x = 0 := by
  have hab := hac.trans_lt hcb
  have hU := H.U_system.continuousOn
  have hV := H.V_system.continuousOn
  have hUs : OuterFirstOrderSystem alpha beta H.U H.ZU (Ioo a b) :=
    fun x hx => H.U_system x (Ioo_subset_Ico_self hx)
  have hVs : OuterFirstOrderSystem alpha beta H.V H.ZV (Ioo a b) :=
    fun x hx => H.V_system x (Ioo_subset_Ico_self hx)
  have hconstV := outerFirstOrderSystem_determinant_Ico hab hu hz hV.1 hV.2 hstate hVs
  have hconstU := outerFirstOrderSystem_determinant_Ico hab hU.1 hU.2 hu hz hUs hstate
  obtain ⟨C, hC⟩ := hnatural
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have hd : d ∈ Ioo a b := ⟨hac.trans_lt hcd, hdb⟩
  have hvalue : u =ᶠ[𝓝 d] fun x => (C * H.scale) * H.V x := by
    filter_upwards [Ioo_mem_nhds hcd hdb] with x hx
    rw [hC x hx, H.V_tail x ⟨hx.1.le, hx.2⟩]
    field_simp [H.scale_pos.ne'] <;> ring
  have hder := ((H.V_system d (Ioo_subset_Ico_self hd)).1.const_mul
    (C * H.scale)).congr_of_eventuallyEq hvalue
  have hzd : z d = (C * H.scale) * H.ZV d := by
    apply mul_left_cancel₀ (hα d ⟨hcd, hdb⟩)
    calc
      alpha d * z d = (C * H.scale) * (alpha d * H.ZV d) :=
        (hstate d hd).1.unique hder
      _ = alpha d * ((C * H.scale) * H.ZV d) := by ring
  have hdetd : u d * H.ZV d - z d * H.V d = 0 := by
    rw [hvalue.eq_of_nhds, hzd]
    ring
  have hdeta : u a * H.ZV a - z a * H.V a = 0 :=
    (hconstV d (Ioo_subset_Ico_self hd)).symm.trans hdetd
  have hva := congrArg Prod.fst H.V_initial
  have hza := congrArg Prod.snd H.V_initial
  change H.V a = H.entrance.1 at hva
  change H.ZV a = H.entrance.2 at hza
  rw [hva, hza] at hdeta
  change H.entrance.1 * u a + H.entrance.2 * z a = 0 at hRobin
  have hu0 : u a = 0 := by
    linear_combination H.entrance.1 * hRobin + H.entrance.2 * hdeta - u a * H.unit
  have hz0 : z a = 0 := by
    linear_combination H.entrance.2 * hRobin - H.entrance.1 * hdeta - z a * H.unit
  intro x hx
  have hVdet : u x * H.ZV x - z x * H.V x = 0 := by
    rw [hconstV x hx, hu0, hz0, zero_mul, zero_mul, sub_self]
  have hUdet : H.U x * z x - H.ZU x * u x = 0 := by
    rw [hconstU x hx, hu0, hz0, mul_zero, mul_zero, sub_self]
  have hdet := H.determinant x hx
  constructor
  · linear_combination -H.U x * hVdet - H.V x * hUdet + u x * hdet
  · linear_combination -H.ZU x * hVdet - H.ZV x * hUdet + z x * hdet

end ContinuousFlexibility.Radial
