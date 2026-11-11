import ContinuousFlexibility.Radial.OuterHomogeneousContinuation
import ContinuousFlexibility.Radial.OuterGreenIntegral

/-!
# Constructing the normalized homogeneous pair on the whole outer region

The natural state is propagated backwards through the actual finite core.
Its full state cannot vanish.  Normalizing that full state and continuing
its perpendicular state gives the two solutions used by the outer Green
kernel.  Neither the construction nor the Wronskian proof divides by the
natural solution's value at the outer entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped Topology

/-- The actual homogeneous pair and its explicit continuation into the tail.
The structure is produced below from finite ODE existence and a deep basis. -/
structure OuterFundamentalStatePair (alpha beta P ZP Q ZQ : ℝ → ℝ) (a c b : ℝ) where
  U : ℝ → ℝ
  ZU : ℝ → ℝ
  V : ℝ → ℝ
  ZV : ℝ → ℝ
  entrance : ℝ × ℝ
  scale : ℝ
  tailA : ℝ
  tailB : ℝ
  unit : entrance.1 ^ 2 + entrance.2 ^ 2 = 1
  scale_pos : 0 < scale
  U_initial : (U a, ZU a) = outerStatePerp entrance
  V_initial : (V a, ZV a) = entrance
  U_system : OuterFirstOrderSystem alpha beta U ZU (Ico a b)
  V_system : OuterFirstOrderSystem alpha beta V ZV (Ico a b)
  U_tail : ∀ x ∈ Ico c b, U x = tailA * P x + tailB * Q x
  ZU_tail : ∀ x ∈ Ico c b, ZU x = tailA * ZP x + tailB * ZQ x
  V_tail : ∀ x ∈ Ico c b, V x = P x / scale
  ZV_tail : ∀ x ∈ Ico c b, ZV x = ZP x / scale
  determinant : ∀ x ∈ Ico a b, U x * ZV x - ZU x * V x = -1

/-- Actual construction of the pair from the regular core and the already
constructed normalized natural and Dirichlet deep-tail solutions. -/
theorem exists_outerFundamentalStatePair {a b c : ℝ} (hac : a ≤ c) (hcb : c < b)
    {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (halpha : ContinuousOn alpha (Icc a c)) (hbeta : ContinuousOn beta (Icc a c))
    (hP : OuterFirstOrderSystem alpha beta P ZP (Ico c b))
    (hQ : OuterFirstOrderSystem alpha beta Q ZQ (Ico c b))
    (hPc : P c = 1) (hQc : Q c = 0) (hZQc : ZQ c ≠ 0) :
    Nonempty (OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) := by
  obtain ⟨vL, zL, hinit, hL⟩ := exists_outerFirstOrder_state hac halpha hbeta c (1, ZP c)
  have hmatch : (vL c, zL c) = (P c, ZP c) := by
    simpa only [hPc] using hinit
  have hnc : (vL c, zL c) ≠ 0 := by
    rw [hinit]
    intro h
    have hf := congrArg Prod.fst h
    norm_num at hf
  have hna : (vL a, zL a) ≠ 0 :=
    outerFirstOrder_state_ne_zero hac halpha hbeta ⟨le_rfl, hac⟩
      ⟨hac, le_rfl⟩ hL hnc
  let v : ℝ × ℝ := outerUnitState (vL a, zL a)
  let t : ℝ := Real.sqrt ((vL a) ^ 2 + (zL a) ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr (outerState_sq_pos hna)
  have hv : v.1 ^ 2 + v.2 ^ 2 = 1 := outerUnitState_unit hna
  let V : ℝ → ℝ := fun x => t⁻¹ * morseGlueCut c vL P x
  let ZV : ℝ → ℝ := fun x => t⁻¹ * morseGlueCut c zL ZP x
  have hVsys : OuterFirstOrderSystem alpha beta V ZV (Ico a b) :=
    (outerFirstOrderSystem_glue hac hcb hL hP hmatch).const_mul t⁻¹
  have hVa : (V a, ZV a) = v := by
    dsimp only [V, ZV, v, t, outerUnitState, morseGlueCut]
    simp only [hac, ite_true]
    apply Prod.ext <;> dsimp only <;> ring
  obtain ⟨U, ZU, A, B, hUa, hUsys, hUtail, hZUtail⟩ :=
    exists_outer_continued_state hac hcb halpha hbeta hP hQ hPc hQc hZQc (outerStatePerp v)
  have hVtail : ∀ x ∈ Ico c b, V x = P x / t := by
    intro x hx
    dsimp only [V]
    rw [morseGlueCut_eq_right_of_matching (congrArg Prod.fst hmatch) hx.1]
    ring
  have hZVtail : ∀ x ∈ Ico c b, ZV x = ZP x / t := by
    intro x hx
    dsimp only [ZV]
    rw [morseGlueCut_eq_right_of_matching (congrArg Prod.snd hmatch) hx.1]
    ring
  have hdet : ∀ x ∈ Ico a b, U x * ZV x - ZU x * V x = -1 := by
    have ha : a ∈ Ico a b := ⟨le_rfl, hac.trans_lt hcb⟩
    have hua : U a = -v.2 := congrArg Prod.fst hUa
    have hza : ZU a = v.1 := congrArg Prod.snd hUa
    have hva : V a = v.1 := congrArg Prod.fst hVa
    have hzva : ZV a = v.2 := congrArg Prod.snd hVa
    intro x hx
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b) hUsys hVsys ha hx,
      hua, hza, hva, hzva]
    nlinarith
  exact ⟨{
    U := U, ZU := ZU, V := V, ZV := ZV, entrance := v, scale := t,
    tailA := A, tailB := B, unit := hv, scale_pos := ht,
    U_initial := hUa, V_initial := hVa, U_system := hUsys, V_system := hVsys,
    U_tail := hUtail, ZU_tail := hZUtail, V_tail := hVtail, ZV_tail := hZVtail,
    determinant := hdet
  }⟩

/-- The natural solution is nonzero at the deep entrance, where it was
normalized before propagation.  Its value at the outer entrance is unrestricted. -/
theorem OuterFundamentalStatePair.V_deep_pos
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hcb : c < b) (hPc : P c = 1) : 0 < F.V c := by
  rw [F.V_tail c ⟨le_rfl, hcb⟩, hPc]
  exact one_div_pos.mpr F.scale_pos

/-- The tail proportionality used by the actual Green block identity. -/
theorem OuterFundamentalStatePair.V_tail_factor
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hcb : c < b) (hPc : P c = 1) :
    ∀ x ∈ Ico c b, F.V x = F.V c * P x := by
  intro x hx
  rw [F.V_tail x hx, F.V_tail c ⟨le_rfl, hcb⟩, hPc]
  ring

/-- The state variables of the constructed pair are the physical scaled fluxes. -/
theorem OuterFundamentalStatePair.flux_states
    {a c b lam : ℝ} {beta w P ZP Q ZQ : ℝ → ℝ}
    (F : OuterFundamentalStatePair (fun x => lam / w x) beta P ZP Q ZQ a c b)
    (hlam : lam ≠ 0) (hw : ∀ x ∈ Ico a b, w x ≠ 0) :
    ∀ x ∈ Ico a b,
      outerFluxState lam w F.U x = (F.U x, F.ZU x) ∧
      outerFluxState lam w F.V x = (F.V x, F.ZV x) := by
  intro x hx
  constructor
  · apply Prod.ext rfl
    change w x * deriv F.U x / lam = F.ZU x
    rw [(F.U_system x hx).1.deriv]
    field_simp [hw x hx, hlam] <;> ring
  · apply Prod.ext rfl
    change w x * deriv F.V x / lam = F.ZV x
    rw [(F.V_system x hx).1.deriv]
    field_simp [hw x hx, hlam] <;> ring

/-- The actual radial Wronskian is exactly minus the frequency scale. -/
theorem OuterFundamentalStatePair.radialWronskian
    {a c b lam : ℝ} {beta w P ZP Q ZQ : ℝ → ℝ}
    (F : OuterFundamentalStatePair (fun x => lam / w x) beta P ZP Q ZQ a c b)
    (hw : ∀ x ∈ Ico a b, w x ≠ 0) :
    ∀ x ∈ Ico a b, radialWronskian w F.U F.V x = -lam := by
  intro x hx
  have hfu : w x * deriv F.U x = lam * F.ZU x := by
    rw [(F.U_system x hx).1.deriv]
    field_simp [hw x hx] <;> ring
  have hfv : w x * deriv F.V x = lam * F.ZV x := by
    rw [(F.V_system x hx).1.deriv]
    field_simp [hw x hx] <;> ring
  calc
    radialWronskian w F.U F.V x =
        F.U x * (w x * deriv F.V x) - (w x * deriv F.U x) * F.V x := by
      unfold radialWronskian
      ring
    _ = lam * (F.U x * F.ZV x - F.ZU x * F.V x) := by rw [hfu, hfv]; ring
    _ = -lam := by rw [F.determinant x hx]; ring

end ContinuousFlexibility.Radial
