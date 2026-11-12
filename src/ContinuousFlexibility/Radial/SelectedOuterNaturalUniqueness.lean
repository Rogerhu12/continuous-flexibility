import ContinuousFlexibility.Radial.SelectedOutwardRegionMeasure
import ContinuousFlexibility.Radial.OuterPhysicalTailUniqueness
import ContinuousFlexibility.Radial.OuterFundamentalPair
import ContinuousFlexibility.Radial.OuterFirstOrderRegularity

/-!
# The actual natural line at the original exterior cut

Classification is applied only on the deep tail. Two conserved full-state
Wronskians propagate that equality through the finite core. Continuity
then includes the regular cut, without imposing a derivative there.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

private theorem selected_two_states_injective {u z U Z p q r s : ℝ}
    (hdet : p * s - q * r ≠ 0)
    (hP : u * q - z * p = U * q - Z * p)
    (hQ : u * s - z * r = U * s - Z * r) : u = U ∧ z = Z := by
  have h₁ : (u - U) * q - (z - Z) * p = 0 := by nlinarith only [hP]
  have h₂ : (u - U) * s - (z - Z) * r = 0 := by nlinarith only [hQ]
  have hu : (u - U) * (p * s - q * r) = 0 := by
    calc
      _ = p * ((u - U) * s - (z - Z) * r) -
          r * ((u - U) * q - (z - Z) * p) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hz : (z - Z) * (p * s - q * r) = 0 := by
    calc
      _ = q * ((u - U) * s - (z - Z) * r) -
          s * ((u - U) * q - (z - Z) * p) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hdet)⟩

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K cut lam : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

local notation "a" => outerTailSign right * cut
local notation "c" => outerTailSign right * entrance
local notation "b" => outerTailSign right * tailPhysicalEndpoint D right
local notation "T" => morsePhysicalDeepTail M D right j start entrance η K
local notation "w" => outerTailOutwardWeight D right
local notation "α" => (fun x => lam / w x)
local notation "β" => (fun x => (j : ℝ) ^ 2 * deriv w x / (lam * x))
local notation "μ" => outerOutwardIntervalMeasure D right (radialTailInterval D right cut)

theorem whole_natural_line
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D) (hac : a < c) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair α β F.P (F.ZP lam) F.Q (F.ZQ lam) a c b)
    {u z : ℝ → ℝ} (hu : ContinuousOn u (Ico a b)) (hz : ContinuousOn z (Ico a b))
    (hsys : OuterFirstOrderSystem α β u z (Ioo a b))
    (hL2 : MemLp u 2 μ) :
    ∃ k : ℝ, ∀ x ∈ Ico a b, u x = k * H.V x ∧ z x = k * H.ZV x := by
  have hg := matchingProfileGeometry hD
  have hep : 0 < entrance := hg.1.trans hentry.1
  have hcb : c < b := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hentry.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hentry.2
  have her : tailPhysicalRadius right (T).entrance = entrance :=
    tailPhysicalRadius_log right hep
  have horder : outerOutwardRadius right cut ≤
      outerOutwardRadius right (tailPhysicalRadius right (T).entrance) := by
    simpa only [her, outerOutwardRadius_eq_sign] using hac.le
  have hm := outerOutwardRegion_restrict_deep hD hphysical horder
  simp only [her, outerOutwardRadius_eq_sign] at hm
  have hdeepLp : MemLp u 2 (outerOutwardTailMeasure D T right) := by
    rw [← hm]
    exact hL2.restrict _
  have hdeep : OuterFirstOrderSystem α β u z (Ico c b) :=
    fun x hx => hsys x ⟨hac.trans_le hx.1, hx.2⟩
  obtain ⟨A, hA⟩ := MorsePhysicalTailBasis.natural_line hg hep hlam hT hη hK F hdeep hdeepLp
  let k : ℝ := A * H.scale
  have hmatch : u c = k * H.V c ∧ z c = k * H.ZV c := by
    rw [H.V_tail c ⟨le_rfl, hcb⟩, H.ZV_tail c ⟨le_rfl, hcb⟩]
    obtain ⟨hu, hz⟩ := hA c ⟨le_rfl, hcb⟩
    constructor
    · rw [hu]
      dsimp only [k]
      field_simp [H.scale_pos.ne'] <;> ring
    · rw [hz]
      dsimp only [k]
      field_simp [H.scale_pos.ne'] <;> ring
  have hU : OuterFirstOrderSystem α β H.U H.ZU (Ioo a b) :=
    fun x hx => H.U_system x (Ioo_subset_Ico_self hx)
  have hV : OuterFirstOrderSystem α β H.V H.ZV (Ioo a b) :=
    fun x hx => H.V_system x (Ioo_subset_Ico_self hx)
  have hkV := hV.const_mul k
  have hc : c ∈ Ioo a b := ⟨hac, hcb⟩
  have heq : EqOn (fun x => (u x, z x))
      (fun x => (k * H.V x, k * H.ZV x)) (Ioo a b) := by
    intro x hx
    have hwu : u x * H.ZU x - z x * H.U x =
        (k * H.V x) * H.ZU x - (k * H.ZV x) * H.U x := by
      rw [outerFirstOrderSystem_state_determinant (convex_Ioo a b) hsys hU hc hx,
        outerFirstOrderSystem_state_determinant (convex_Ioo a b) hkV hU hc hx,
        hmatch.1, hmatch.2]
    have hwv : u x * H.ZV x - z x * H.V x =
        (k * H.V x) * H.ZV x - (k * H.ZV x) * H.V x := by
      rw [outerFirstOrderSystem_state_determinant (convex_Ioo a b) hsys hV hc hx,
        outerFirstOrderSystem_state_determinant (convex_Ioo a b) hkV hV hc hx,
        hmatch.1, hmatch.2]
    have hdet : H.U x * H.ZV x - H.ZU x * H.V x ≠ 0 := by
      rw [H.determinant x (Ioo_subset_Ico_self hx)]
      norm_num
    obtain ⟨hv, hz⟩ := selected_two_states_injective hdet hwu hwv
    exact Prod.ext hv hz
  have hclosure : Ico a b ⊆ closure (Ioo a b) := by
    rw [closure_Ioo (hac.trans hcb).ne]
    exact Ico_subset_Icc_self
  have heq' := heq.of_subset_closure (hu.prodMk hz)
    ((continuousOn_const.mul H.V_system.continuousOn.1).prodMk
      (continuousOn_const.mul H.V_system.continuousOn.2))
    Ioo_subset_Ico_self hclosure
  exact ⟨k, fun x hx => ⟨congrArg Prod.fst (heq' hx), congrArg Prod.snd (heq' hx)⟩⟩

theorem whole_robin_unique
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D) (hac : a < c) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair α β F.P (F.ZP lam) F.Q (F.ZQ lam) a c b)
    {u z : ℝ → ℝ} (hu : ContinuousOn u (Ico a b)) (hz : ContinuousOn z (Ico a b))
    (hsys : OuterFirstOrderSystem α β u z (Ioo a b))
    (hL2 : MemLp u 2 μ) (hRobin : outerStatePair H.entrance (u a, z a) = 0) :
    ∀ x ∈ Ico a b, u x = 0 ∧ z x = 0 := by
  obtain ⟨k, hk⟩ := F.whole_natural_line hD hcut hentry hac hlam hT hphysical hη hK
    H hu hz hsys hL2
  have hab : a < b := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hcut.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hcut.2
  have hka := hk a ⟨le_rfl, hab⟩
  have hzero : k = 0 := by
    have hv : H.V a = H.entrance.1 := congrArg Prod.fst H.V_initial
    have hz : H.ZV a = H.entrance.2 := congrArg Prod.snd H.V_initial
    change H.entrance.1 * u a + H.entrance.2 * z a = 0 at hRobin
    rw [hka.1, hka.2, hv, hz] at hRobin
    have hh : k * (H.entrance.1 ^ 2 + H.entrance.2 ^ 2) = 0 := by
      nlinarith only [hRobin]
    simpa only [H.unit, mul_one] using hh
  intro x hx
  simpa only [hzero, zero_mul] using hk x hx

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
