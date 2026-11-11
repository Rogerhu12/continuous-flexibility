import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.CircleWeakPrimitive
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual physical representatives of canonical L² data

The almost-everywhere unique interval cover in N04 already implies that
distinct physical piece interiors are disjoint. A periodic representative
on each canonical cylinder can therefore be reconstructed on the physical
pieces without ambiguity. These formulas verify the actual canonical
height and source identities. No physical differential equation or
transmission condition is inferred from representation alone.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- Every canonical L² representative is extended using the original
half-period, without assumptions on its values outside the measured tile. -/
def n06CanonicalPeriodize (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  anglePeriodize (fun θ => f (p.1, θ)) p.2

theorem n06CanonicalPeriodize_periodic (f : PolarPoint → ℝ) :
    Function.Periodic (n06CanonicalPeriodize f) (0, Real.pi) := by
  intro p
  change anglePeriodize (fun θ => f (p.1 + 0, θ)) (p.2 + Real.pi) = _
  rw [add_zero, anglePeriodize_periodic]
  rfl

theorem n06CanonicalPeriodize_eq (f : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p.2 ∈ Ioc (0 : ℝ) Real.pi) : n06CanonicalPeriodize f p = f p :=
  anglePeriodize_eqOn (fun θ => f (p.1, θ)) hp

theorem n06CanonicalPeriodize_ae {S : PhysicalSpacesData} {K : CanonicalData S}
    (m : ℕ) (f : PolarPoint → ℝ) :
    n06CanonicalPeriodize f =ᵐ[canonicalMeasure S K m] f := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact n06CanonicalPeriodize_eq f hp.2

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Uniqueness off a null set rules out overlap of two open physical pieces. -/
theorem n06_physicalPiece_pairwiseDisjoint
    (hN04 : N04Properties D T S C L K base loss ε) :
    Pairwise (fun m n : ℕ =>
      Disjoint (Ioo (K.physicalLeft m) (K.physicalRight m))
        (Ioo (K.physicalLeft n) (K.physicalRight n))) := by
  obtain ⟨_, _, _, hpieces, _, _, ⟨E, hE, hcover⟩, _⟩ := hN04
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro r hrm hrn
  let O : Set ℝ := Ioo (K.physicalLeft m) (K.physicalRight m) ∩
    Ioo (K.physicalLeft n) (K.physicalRight n)
  have hOE : O ⊆ E := by
    intro x hx
    by_contra hxE
    obtain ⟨k, hk, huniq⟩ := hcover x ⟨(hpieces m).2.2 hx.1, hxE⟩
    exact hmn ((huniq m hx.1).trans (huniq n hx.2).symm)
  have hzero : volume O = 0 := measure_mono_null hOE hE
  have hpos : volume O ≠ 0 :=
    (isOpen_Ioo.inter isOpen_Ioo).measure_ne_zero volume ⟨r, hrm, hrn⟩
  exact hpos hzero

/-- The selected piece depends only on the physical radial coordinate. -/
def n06PhysicalPieceIndex (K : CanonicalData S) (r : ℝ) : ℕ := by
  classical
  exact if h : ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then
    h.choose else 0

theorem n06PhysicalPieceIndex_eq
    (hN04 : N04Properties D T S C L K base loss ε)
    {r : ℝ} {m : ℕ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n06PhysicalPieceIndex K r = m := by
  classical
  have hex : ∃ n, r ∈ Ioo (K.physicalLeft n) (K.physicalRight n) := ⟨m, hr⟩
  simp only [n06PhysicalPieceIndex, dite_eq_left hex]
  by_contra hne
  exact (Set.disjoint_left.mp (n06_physicalPiece_pairwiseDisjoint hN04 hne))
    hex.choose_spec hr

/-- Reconstruct a family of actual canonical fields with a specified physical
weight, and set it to zero off the union of the open physical pieces. -/
def n06PhysicalReconstruct (K : CanonicalData S) (z : AnnularState S × ℝ)
    (f : ℕ → PolarPoint → ℝ) (w : ℕ → PolarPoint → ℝ) (p : PolarPoint) : ℝ := by
  classical
  exact if ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then
    let m := n06PhysicalPieceIndex K p.1
    w m p * n06CanonicalPeriodize (f m) (K.chart z m p)
  else 0

theorem n06PhysicalReconstruct_on_piece
    (hN04 : N04Properties D T S C L K base loss ε)
    (z : AnnularState S × ℝ) (f w : ℕ → PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n06PhysicalReconstruct K z f w p =
      w m p * n06CanonicalPeriodize (f m) (K.chart z m p) := by
  classical
  have hex : ∃ n, p.1 ∈ Ioo (K.physicalLeft n) (K.physicalRight n) := ⟨m, hp.1⟩
  simp only [n06PhysicalReconstruct, ite_eq_left hex, n06PhysicalPieceIndex_eq hN04 hp.1]

/-- The reconstruction has the expected value on the actual inverse chart. -/
theorem n06PhysicalReconstruct_inverseChart
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f w : ℕ → PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hθ : p.2 ∈ Ioc (0 : ℝ) Real.pi) :
    n06PhysicalReconstruct K z f w (K.inverseChart z m p) =
      w m (K.inverseChart z m p) * f m p := by
  have hfull := hN04
  obtain ⟨_, _, _, _, _, _, _, hcharts, _⟩ := hfull
  obtain ⟨_, himap, _, hright, _, _, _, _⟩ := hcharts z hz hs m
  rw [n06PhysicalReconstruct_on_piece hN04 z f w (himap hp), hright p hp,
    n06CanonicalPeriodize_eq _ hθ]

/-- Periodic weights give a periodic physical reconstruction; the chosen
piece and the outside value are unchanged by an angular translation. -/
theorem n06PhysicalReconstruct_periodic
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f w : ℕ → PolarPoint → ℝ)
    (hw : ∀ m p, p ∈ physicalPieceOpen S K m → w m (p + (0, Real.pi)) = w m p) :
    Function.Periodic (n06PhysicalReconstruct K z f w) (0, Real.pi) := by
  classical
  have hfull := hN04
  obtain ⟨_, _, _, _, _, _, _, hcharts, _⟩ := hfull
  intro p
  by_cases hex : ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · obtain ⟨m, hm⟩ := hex
    have hp : p ∈ physicalPieceOpen S K m := ⟨hm, mem_univ _⟩
    have hp' : p + (0, Real.pi) ∈ physicalPieceOpen S K m := by
      exact ⟨by simpa only [Prod.fst_add, add_zero] using hm, mem_univ _⟩
    obtain ⟨_, _, _, _, _, _, _, hchart⟩ := hcharts z hz hs m
    rw [n06PhysicalReconstruct_on_piece hN04 z f w hp',
      n06PhysicalReconstruct_on_piece hN04 z f w hp, hw m p hp,
      (hchart p hp).2.2.1, n06CanonicalPeriodize_periodic]
  · simp only [n06PhysicalReconstruct, Prod.fst_add, add_zero, ite_eq_right hex]

/-- The actual reconstructed height, including its left constant tail. -/
def n06PhysicalHeight (K : CanonicalData S) (z : AnnularState S × ℝ)
    (W : ℕ → PolarPoint → ℝ) (aL : ℝ) (p : PolarPoint) : ℝ :=
  n06PhysicalReconstruct K z W (K.height z) p + aL * S.chiLeft p.1

/-- The actual inverse source transform on the physical piece cover. -/
def n06PhysicalSource (K : CanonicalData S) (z : AnnularState S × ℝ)
    (F : ℕ → PolarPoint → ℝ) : PolarPoint → ℝ :=
  n06PhysicalReconstruct K z F
    (fun m p => |planeJacobian (K.chart z m) p| / K.height z m p)

/-- The named reconstruction satisfies both actual canonical identities.
The separate weak-equation and transmission obligations remain. -/
theorem n06_physical_representation
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (U : CanonicalUnknown S K) (F : CanonicalSequence S K) :
    HasCanonicalRepresentation D S C K z U F
      (n06PhysicalHeight K z (fun m => (U.1 m : PolarPoint → ℝ)) U.2.1)
      (n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ))) ∧
      Function.Periodic
        (n06PhysicalHeight K z (fun m => (U.1 m : PolarPoint → ℝ)) U.2.1)
        (0, Real.pi) := by
  let W : ℕ → PolarPoint → ℝ := fun m => (U.1 m : PolarPoint → ℝ)
  let G : ℕ → PolarPoint → ℝ := fun m => (F m : PolarPoint → ℝ)
  let η : PolarPoint → ℝ := fun p =>
    n06PhysicalReconstruct K z W (K.height z) p + U.2.1 * S.chiLeft p.1
  let f : PolarPoint → ℝ := n06PhysicalReconstruct K z G
    (fun m p => |planeJacobian (K.chart z m) p| / K.height z m p)
  have hfull := hN04
  obtain ⟨_, _, _, _, _, _, _, hcharts, _⟩ := hfull
  have hηperiod : Function.Periodic η (0, Real.pi) := by
    have hWperiod := n06PhysicalReconstruct_periodic hN04 hz hs W (K.height z)
      (fun m p hp => ((hcharts z hz hs m).2.2.2.2.2.2.2 p hp).2.2.2)
    intro p
    change n06PhysicalReconstruct K z W (K.height z) (p + (0, Real.pi)) +
      U.2.1 * S.chiLeft (p + (0, Real.pi)).1 = _
    rw [hWperiod p, Prod.fst_add, add_zero]
  refine ⟨⟨?_, ?_⟩, hηperiod⟩
  · intro m
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    obtain ⟨_, himap, _, _, _, _, _, hheight⟩ := hcharts z hz hs m
    have hn := (hheight _ (himap hpc)).1.ne'
    have hrec := n06PhysicalReconstruct_inverseChart hN04 hz hs W (K.height z) hpc hp.2
    change U.1 m p =
      (n06PhysicalReconstruct K z W (K.height z) (K.inverseChart z m p) +
        U.2.1 * S.chiLeft (K.inverseChart z m p).1 -
        U.2.1 * S.chiLeft (K.inverseChart z m p).1) /
          K.height z m (K.inverseChart z m p)
    rw [hrec]
    dsimp only [W]
    field_simp
    ring
  · intro m
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    obtain ⟨_, himap, _, _, _, _, _, hheight⟩ := hcharts z hz hs m
    have hh := (hheight _ (himap hpc)).1.ne'
    have hj := abs_ne_zero.mpr (hheight _ (himap hpc)).2.1
    have hrec := n06PhysicalReconstruct_inverseChart hN04 hz hs G
      (fun m p => |planeJacobian (K.chart z m) p| / K.height z m p) hpc hp.2
    change F m p = K.height z m (K.inverseChart z m p) *
      n06PhysicalReconstruct K z G
        (fun m p => |planeJacobian (K.chart z m) p| / K.height z m p)
        (K.inverseChart z m p) / |planeJacobian (K.chart z m) (K.inverseChart z m p)|
    rw [hrec]
    dsimp only [G]
    field_simp

/-- Every canonical unknown and source have actual physical representatives. -/
theorem n06_exists_physical_representation
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (U : CanonicalUnknown S K) (F : CanonicalSequence S K) :
    ∃ η f : PolarPoint → ℝ, HasCanonicalRepresentation D S C K z U F η f ∧
      Function.Periodic η (0, Real.pi) :=
  ⟨_, _, (n06_physical_representation hN04 hz hs U F).1,
    (n06_physical_representation hN04 hz hs U F).2⟩

end ContinuousFlexibility.Statements
