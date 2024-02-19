import Mathlib.Logic.Equiv.TransferInstance
import Thermodynamics.MathLemma
import Thermodynamics.ZerothLaw

/-!
# Thermodynamic Cycles and the FIRST Law

This file defines
* the notion of abstract thermodynamic `Cycle`s, which satisfy the first law
* some specific types of `Cycle`s, including
  `OneRsvCycle`, `AbsRelCycle`, `class EngineCycle`,
  `UsualEngineCycle`, `UsualPumpCycle`
* the connection (`add`), scaling (`smul`), and reversion of `Cycle`s
and proves
* some basic properties of the various types of `Cycle`s
-/

noncomputable section

namespace Thermodynamics

/-!
## General abstract `Cycle`

According to the first law, a thermodynamic `Cycle` can be regarded as a heat-work conversion.
* Abstract `Cycle`s are defined to be the equivalence class of concrete cycles
  that have the same net heat-work conversion.
* `Cycle`s need not to satisfy the second law.
---------------------------------------------------------------------------------------------------/

/-- Abstrct `Cycle` (denoted by `H`) :
    finitely many `𝓣`s PROVIDE heat `𝓠 𝓣`, and `H` DOES work `𝓦`, satisfying the first law -/
structure Cycle where
  𝓠 : Reservoir →₀ ℝ
  𝓦 : ℝ
  energy_conserv : 𝓠.sum_image - 𝓦 = 0

namespace Cycle

variable (H : Cycle)
/-- `abs`orbed heat `Qabs = ∑(+𝓠 > 0)` -/
def Qabs : ℝ := H.𝓠.support.sum (fun 𝓣 ↦ max (H.𝓠 𝓣) 0)
lemma Qabs_nonneg : 0 ≤ H.Qabs := by simp [Qabs, Finset.sum_nonneg]
/-- `rel`eased heat `Qrel = ∑(-𝓠 > 0)` -/
def Qrel : ℝ := H.𝓠.support.sum (fun 𝓣 ↦ max (- H.𝓠 𝓣) 0)
lemma Qrel_nonneg : 0 ≤ H.Qrel := by simp [Qrel, Finset.sum_nonneg]

variable {H}
lemma 𝓦_from_𝓠 : H.𝓦 = H.𝓠.sum_image := by
  have := H.energy_conserv; rw [sub_eq_zero] at this; rw [this]
lemma 𝓠_from_Qabs_Qrel : H.𝓠.sum_image = H.Qabs - H.Qrel := by simp [Qabs, Qrel, ←Finset.sum_sub_distrib]
lemma 𝓦_from_Qabs_Qrel : H.𝓦   = H.Qabs - H.Qrel := by rw [𝓦_from_𝓠, 𝓠_from_Qabs_Qrel]
lemma Qabs_from_𝓦_Qrel : H.Qabs = H.𝓦   + H.Qrel := by simp [𝓦_from_Qabs_Qrel]
lemma Qrel_from_Qabs_𝓦 : H.Qrel = H.Qabs - H.𝓦   := by simp [𝓦_from_Qabs_Qrel]

/-- A `Cycle` is fully specified by `𝓠`  -/
@[reducible] def equiv_𝓠 : (Reservoir →₀ ℝ) ≃ Cycle where
  toFun := fun 𝓠 ↦ {
    𝓠 := 𝓠
    𝓦 := 𝓠.sum_image
    energy_conserv := by rw [sub_self]
  }
  invFun := fun H ↦ H.𝓠
  left_inv := fun H ↦ rfl
  right_inv := fun H ↦ by
    let ⟨𝓠,𝓦,energy_conserv⟩ := H; simp
    rwa [sub_eq_zero] at energy_conserv
/-- `Cycle` forms an `AddCommGroup`.
* adding two `Cycle`s means connecting them
* negating a `Cycle` means reversing it
-/
instance : AddCommGroup Cycle := Equiv.addCommGroup equiv_𝓠.symm
/-- `Cycle` forms a real vector space.
* multiplying a `Cycle` with `c ∈ ℝ` means scaling it `c` times
-/
instance : Module ℝ     Cycle := Equiv.module ℝ    equiv_𝓠.symm

variable {H₁ H₂ : Cycle} {c : ℝ}
@[simp] lemma 𝓦_add : (H₁ + H₂).𝓦 = H₁.𝓦 + H₂.𝓦 := calc
  _ = H₁.𝓠.sum_image + H₂.𝓠.sum_image := Finsupp.sum_image_add
  _ = H₁.𝓦 + H₂.𝓦 := by simp [𝓦_from_𝓠]
@[simp] lemma 𝓦_smul : (c • H).𝓦 = c * H.𝓦 := calc
  _ = c * H.𝓠.sum_image := Finsupp.sum_image_smul
  _ = c * H.𝓦 := by rw [𝓦_from_𝓠]
@[simp] lemma rev_𝓦 : (-H).𝓦 = -H.𝓦 := calc
  _ = ((-1:ℝ) • H).𝓦 := by simp
  _ = (-1:ℝ) * H.𝓦 := by rw [𝓦_smul]
  _ = -H.𝓦 := by simp
@[simp] lemma Qabs_smul_pos (hc : 0 < c) : (c • H).Qabs = c * H.Qabs := calc
  _ = (c • H.𝓠).support.sum (fun 𝓣 ↦ max ((c • H).𝓠 𝓣) 0) := rfl
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ max ((c • H).𝓠 𝓣) 0) := by simp [ne_of_gt hc]
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ max  (c *  H.𝓠 𝓣) 0) := rfl
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ c * max   (H.𝓠 𝓣) 0) := by simp [le_of_lt hc]
  _ =  c *  H.𝓠.support.sum (fun 𝓣 ↦     max   (H.𝓠 𝓣) 0) := by rw [Finset.mul_sum]
  _ =  c *  H.Qabs := rfl
@[simp] lemma Qrel_smul_pos (hc : 0 < c) : (c • H).Qrel = c * H.Qrel := calc
  _ = (c • H.𝓠).support.sum (fun 𝓣 ↦ max (- (c • H).𝓠 𝓣) 0) := rfl
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ max (- (c • H).𝓠 𝓣) 0) := by simp [ne_of_gt hc]
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ max (- (c * H.𝓠 𝓣)) 0) := rfl
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ max (c * (- H.𝓠 𝓣)) 0) := by simp
  _ =       H.𝓠.support.sum (fun 𝓣 ↦ c * max ((- H.𝓠 𝓣)) 0) := by simp only [le_of_lt hc, Real.max_mul_nonneg_zero]
  _ =  c *  H.𝓠.support.sum (fun 𝓣 ↦     max ((- H.𝓠 𝓣)) 0) := by rw [Finset.mul_sum]
  _ =  c *  H.Qrel := rfl
lemma rev_Qabs : (-H).Qabs = H.Qrel := calc
  _ = (-H.𝓠).support.sum (fun 𝓣 ↦ max ((-H).𝓠 𝓣) 0) := rfl
  _ =    H.𝓠.support.sum (fun 𝓣 ↦ max ((-H).𝓠 𝓣) 0) := by simp
  _ = H.Qrel := rfl
lemma rev_Qrel : (-H).Qrel = H.Qabs := calc
  _ = (-H.𝓠).support.sum (fun 𝓣 ↦ max (-(-H).𝓠 𝓣) 0) := rfl
  _ =    H.𝓠.support.sum (fun 𝓣 ↦ max (-(-H).𝓠 𝓣) 0) := by simp
  _ =    H.𝓠.support.sum (fun 𝓣 ↦ max (- - H.𝓠 𝓣) 0) := rfl
  _ =    H.𝓠.support.sum (fun 𝓣 ↦ max (    H.𝓠 𝓣) 0) := by simp
  _ = H.Qabs := rfl

end Cycle

/-!
## Some types of abstract `Cycle`s
---------------------------------------------------------------------------------------------------/

/-!
### `OneRsvCycle`
-/

/-- `Cycle`s that exchange heat with only one `Reservoir` -/
structure OneRsvCycle (𝓣 : Reservoir) extends Cycle where
  one_rsv : 𝓠.support = {𝓣}

namespace OneRsvCycle
variable {𝓣 : Reservoir} {H : OneRsvCycle 𝓣}

lemma Qabs_one_rsv : H.Qabs = max (  H.𝓠 𝓣) 0 := by simp [Cycle.Qabs, one_rsv]
lemma Qrel_one_rsv : H.Qrel = max (- H.𝓠 𝓣) 0 := by simp [Cycle.Qrel, one_rsv]
/-- `𝓦` is `conv`erted from/to only one rsv. -/
lemma 𝓦_conv_one_rsv : H.𝓦 = H.𝓠 𝓣 := by simp [Cycle.𝓦_from_𝓠, Finsupp.sum_image, one_rsv]

lemma toCycle_inj : Function.Injective (fun H : OneRsvCycle 𝓣 ↦ H.toCycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩ ↦ by simp
instance : SMul ℝ>0 (OneRsvCycle 𝓣) where
  smul := fun c H ↦ {
    (c:ℝ) • H.toCycle with
    one_rsv := calc
      _ = ((c:ℝ) • H.toCycle.𝓠).support := rfl
      _ =           H.toCycle.𝓠.support := by simp [ne_of_gt c.property]
      _ = {𝓣} := H.one_rsv
  }

end OneRsvCycle

/-!
### `AbsRelCycle`
-/

/-- `Cycle`s that absorb heat `Qabs > 0` from rsv `𝓐` and release heat `Qrel > 0` to rsv `𝓡` -/
structure AbsRelCycle (𝓐 𝓡 : Reservoir) extends Cycle where
  two_rsv : 𝓠.support = {𝓐, 𝓡} ∧ 𝓐 ≠ 𝓡
  do_abs_rsv : 0 < 𝓠 𝓐 -- does absorb  heat from `𝓐`
  do_rel_rsv : 𝓠 𝓡 < 0 -- does release heat to   `𝓡`

namespace AbsRelCycle

variable {𝓐 𝓡 : Reservoir} {H : AbsRelCycle 𝓐 𝓡}
lemma Qabs_one_rsv : H.Qabs = H.𝓠 𝓐 := calc
  _ = ({𝓐, 𝓡}:Finset _).sum (fun 𝓣 ↦ max (H.𝓠 𝓣) 0) := by simp [Cycle.Qabs, two_rsv]
  _ = H.𝓠 𝓐 := by
    rw [Finset.sum_pair]
    . have h𝓐 : max (H.𝓠 𝓐) 0 = H.𝓠 𝓐 := by simp [le_of_lt H.do_abs_rsv]
      have h𝓡 : max (H.𝓠 𝓡) 0 =      0 := by simp [le_of_lt H.do_rel_rsv]
      simp [h𝓐, h𝓡]
    . exact H.two_rsv.2
lemma Qrel_one_rsv : H.Qrel = - H.𝓠 𝓡 := calc
  _ = ({𝓐, 𝓡}:Finset _).sum (fun 𝓣 ↦ max (- H.𝓠 𝓣) 0) := by simp [Cycle.Qrel, two_rsv]
  _ = - H.𝓠 𝓡 := by
    rw [Finset.sum_pair]
    . have h𝓐 : max (- H.𝓠 𝓐) 0 =       0 := by simp [le_of_lt H.do_abs_rsv]
      have h𝓡 : max (- H.𝓠 𝓡) 0 = - H.𝓠 𝓡 := by simp [le_of_lt H.do_rel_rsv]
      simp [h𝓐, h𝓡]
    . exact H.two_rsv.2
lemma do_abs : 0 < H.Qabs := calc
  _ = H.𝓠 𝓐 := Qabs_one_rsv
  _ > 0 := H.do_abs_rsv
lemma do_rel : 0 < H.Qrel := calc
  _ = - H.𝓠 𝓡 := Qrel_one_rsv
  _ > 0 := by simp [do_rel_rsv]
lemma 𝓦_from_two_rsv : H.𝓦 = (H.𝓠 𝓐) + (H.𝓠 𝓡) := calc
  _ =  H.Qabs  -  H.Qrel := Cycle.𝓦_from_Qabs_Qrel
  _ = (H.𝓠 𝓐) + (H.𝓠 𝓡) := by simp [Qabs_one_rsv, Qrel_one_rsv]
lemma Qabs_lt_Qrel_iff_consume_work : (H.Qabs < H.Qrel) ↔ (H.𝓦 < 0) := by
  constructor
  . intro do_pump
    calc
      _ = H.Qabs - H.Qrel := Cycle.𝓦_from_Qabs_Qrel
      _ < 0 := by simp [do_pump]
  . intro consume_work
    rw [Cycle.𝓦_from_Qabs_Qrel] at consume_work
    simpa using consume_work

lemma toCycle_inj : Function.Injective (fun H : AbsRelCycle 𝓐 𝓡 ↦ H.toCycle) :=
  λ ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ ↦ by simp

variable {H₁ H₂ : AbsRelCycle 𝓐 𝓡}
lemma eq_of_Q_eq (habs : H₁.Qabs = H₂.Qabs) (hrel : H₁.Qrel = H₂.Qrel) : H₁ = H₂ := by
  suffices H₁.𝓠 = H₂.𝓠 from by
    apply toCycle_inj; apply Cycle.equiv_𝓠.symm.injective
    exact this
  apply Finsupp.ext_iff'.mpr; constructor
  . simp [two_rsv]
  . simp [two_rsv]; constructor
    . rw [←H₁.Qabs_one_rsv, ←H₂.Qabs_one_rsv]; exact habs
    . rw [H₁.Qrel_one_rsv, H₂.Qrel_one_rsv] at hrel; simpa using hrel
lemma eq_of_Qabs_𝓦_eq (hQabs : H₁.Qabs = H₂.Qabs) (h𝓦 : H₁.𝓦 = H₂.𝓦) : H₁ = H₂ := by
  refine eq_of_Q_eq hQabs ?_
  rw [H₁.𝓦_from_Qabs_Qrel, H₂.𝓦_from_Qabs_Qrel] at h𝓦
  linarith

instance : Add (AbsRelCycle 𝓐 𝓡) where
  add := fun H₁ H₂ ↦
    have := H₁.do_abs_rsv; have := H₁.do_rel_rsv
    have := H₂.do_abs_rsv; have := H₂.do_rel_rsv
    { H₁.toCycle + H₂.toCycle with
      two_rsv := by
        constructor
        . apply Finsupp.support_add_exact
          . simp; constructor
            . linarith
            . linarith
          . have := calc (H₁.𝓠.support ∪ H₂.𝓠.support) \ {𝓐, 𝓡}
              _ = ({𝓐, 𝓡} ∪ {𝓐, 𝓡}) \ {𝓐, 𝓡} := by rw [H₁.two_rsv.1, H₂.two_rsv.1]
              _ = ∅ := by simp
            simp [this]
        . exact H₁.two_rsv.2
      do_abs_rsv := calc (H₁.toCycle + H₂.toCycle).𝓠 𝓐
        _ = H₁.𝓠 𝓐 + H₂.𝓠 𝓐 := rfl
        _ > 0 := by linarith
      do_rel_rsv := calc (H₁.toCycle + H₂.toCycle).𝓠 𝓡
        _ = H₁.𝓠 𝓡 + H₂.𝓠 𝓡 := rfl
        _ < 0 := by linarith
    }
instance : AddCommSemigroup (AbsRelCycle 𝓐 𝓡) :=
  Function.Injective.addCommSemigroup _ toCycle_inj (λ _ _ ↦ rfl)
instance : SMul ℝ>0 (AbsRelCycle 𝓐 𝓡) where
  smul := fun c H ↦ {
    c.val • H.toCycle with
    two_rsv := by
      constructor
      . simp
        calc (c.val • H.toCycle).𝓠.support
          _ = (c.val • H.𝓠).support := rfl
          _ =          H.𝓠.support := by simp [Finsupp.support_smul_eq, ne_of_gt c.property]
          _ = {𝓐, 𝓡} := H.two_rsv.1
      . exact H.two_rsv.2
    do_abs_rsv := calc (c.val • H.toCycle).𝓠 𝓐
      _ = c * H.𝓠 𝓐 := rfl
      _ > 0 := by simp [c.property, do_abs_rsv]
    do_rel_rsv := calc (c.val • H.toCycle).𝓠 𝓡
      _ = c * H.𝓠 𝓡 := rfl
      _ < 0 := mul_neg_of_pos_of_neg c.property H.do_rel_rsv
  }

/-- The reverse of an `AbsRelCycle 𝓐 𝓡` is an `AbsRelCycle 𝓡 𝓐`. -/
@[reducible] def rev (H : AbsRelCycle 𝓐 𝓡) : AbsRelCycle 𝓡 𝓐 := {
  -H.toCycle with
  two_rsv := by
    constructor
    . calc (-H.toCycle).𝓠.support
        _ = (-H.𝓠).support := rfl
        _ = (H.𝓠).support := by rw [Finsupp.support_neg]
        _ = {𝓡, 𝓐} := by
          rw [H.two_rsv.1]
          ext; simp; tauto
    . exact H.two_rsv.2.symm
  do_abs_rsv := calc (-H.toCycle).𝓠 𝓡
    _ = - H.𝓠 𝓡 := rfl
    _ = H.Qrel := AbsRelCycle.Qrel_one_rsv.symm
    _ > 0 := H.do_rel
  do_rel_rsv := calc (-H.toCycle).𝓠 𝓐
    _ = - H.𝓠 𝓐 := rfl
    _ = - H.Qabs := by rw [AbsRelCycle.Qabs_one_rsv]
    _ < 0 := by simpa using AbsRelCycle.do_abs
}

end AbsRelCycle

/-!
### `EngineCycle` class
-/

/-- `Cycle`s that do positive work -/
class EngineCycle (H : Cycle) where
  do_work : 0 < H.𝓦

namespace Cycle
variable {H : Cycle} [EngineCycle H]

lemma engine_do_work : 0 < H.𝓦 := EngineCycle.do_work
lemma engine_do_abs : 0 < H.Qabs := calc
  _ = H.𝓦 + H.Qrel := H.Qabs_from_𝓦_Qrel
  _ > 0 := by
    have := H.engine_do_work; have := H.Qrel_nonneg
    positivity

/-- `eff`iciency of `engine_cycle` -/
def eff (H : Cycle) [EngineCycle H] : ℝ := H.𝓦 / H.Qabs
lemma eff_from_Qabs_Qrel : H.eff = 1 - H.Qrel / H.Qabs := calc
  _ = H.𝓦 / H.Qabs := rfl
  _ = ( H.Qabs - H.Qrel ) / H.Qabs := by rw [Cycle.𝓦_from_Qabs_Qrel]
  _ = 1 - H.Qrel / H.Qabs := by field_simp [ne_of_gt H.engine_do_abs]
lemma 𝓦_from_eff_Qabs : H.𝓦 = H.eff * H.Qabs := symm <| calc
  _ = H.𝓦 / H.Qabs * H.Qabs := rfl
  _ = H.𝓦 := by field_simp [ne_of_gt H.engine_do_abs]
lemma Qabs_from_𝓦_eff : H.Qabs = H.𝓦 / H.eff := symm <| calc
  _ = H.𝓦 / ( H.𝓦 / H.Qabs ) := rfl
  _ = H.Qabs := by field_simp [ne_of_gt H.engine_do_work]; ring
lemma eff_pos    : 0 < H.eff := by
  have := H.engine_do_work; have := H.engine_do_abs
  unfold eff; positivity
lemma eff_le_one : H.eff ≤ 1 := calc H.eff
  _ = 1 - H.Qrel / H.Qabs := H.eff_from_Qabs_Qrel
  _ ≤ 1 := by
    simp
    have := H.Qrel_nonneg; have := H.engine_do_abs
    positivity

variable {H₁ H₂ : Cycle} [EngineCycle H₁] [EngineCycle H₂]
instance engine_add : EngineCycle (H₁ + H₂) where
  do_work := calc (H₁ + H₂).𝓦
    _ = H₁.𝓦 + H₂.𝓦 := by simp
    _ > 0 := by
      have := H₁.engine_do_work; have := H₂.engine_do_work
      positivity
variable {c : ℝ} [hc : Fact (0 < c)]
instance engine_smul_pos : EngineCycle (c • H) where
  do_work := calc (c • H).𝓦
    _ = c * H.𝓦 := by simp
    _ > 0 := by
      have := hc.out; have := H.engine_do_work
      positivity
lemma eff_smul_pos : (c • H).eff = H.eff := calc
  _ = (c • H).𝓦 / (c • H).Qabs := rfl
  _ = (c * H.𝓦) / (c * H.Qabs) := by simp [hc.out]
  _ =      H.𝓦  /      H.Qabs  := by
    field_simp [ne_of_gt hc.out, ne_of_gt H.engine_do_abs]; ring
  _ = H.eff := rfl

end Cycle

/-!
### `UsualEngineCycle`
-/

/-- `AbsRelCycle`s that abs from hotter `𝓗`, rel to colder `𝓒`, and do positive work -/
structure UsualEngineCycle {𝓗 𝓒 : Reservoir} (_: 𝓒 < 𝓗) extends (AbsRelCycle 𝓗 𝓒) where
  do_work : 0 < 𝓦

namespace UsualEngineCycle
variable {𝓗 𝓒} {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H : UsualEngineCycle 𝓒_lt_𝓗}

instance : EngineCycle H.toCycle where do_work := H.do_work
lemma eff_lt_one : H.eff < 1 := calc H.eff
  _ = 1 - H.Qrel / H.Qabs := Cycle.eff_from_Qabs_Qrel
  _ < 1 := by
    simp
    have := H.do_rel; have := H.engine_do_abs
    positivity
lemma eff_from_𝓦_𝓠 : H.eff = H.𝓦 / (H.𝓠 𝓗) := calc
  _ = H.𝓦 / H.Qabs := rfl
  _ = H.𝓦 / (H.𝓠 𝓗) := by rw [AbsRelCycle.Qabs_one_rsv]
lemma eff_from_𝓠 : H.eff = 1 - (- H.𝓠 𝓒)/(H.𝓠 𝓗) := calc
  _ = 1 - H.Qrel / H.Qabs := Cycle.eff_from_Qabs_Qrel
  _ = 1 - (- H.𝓠 𝓒)/(H.𝓠 𝓗) := by rw [AbsRelCycle.Qabs_one_rsv, AbsRelCycle.Qrel_one_rsv]

lemma toAbsRelCycle_inj :
  Function.Injective (fun H : UsualEngineCycle 𝓒_lt_𝓗 ↦ H.toAbsRelCycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩ ↦ by simp
instance : Add (UsualEngineCycle 𝓒_lt_𝓗) where
  add := fun H₁ H₂ ↦ {
    H₁.toAbsRelCycle + H₂.toAbsRelCycle,
    @Cycle.engine_add H₁.toCycle H₂.toCycle _ _ with
  }
instance : AddCommSemigroup (UsualEngineCycle 𝓒_lt_𝓗) :=
  Function.Injective.addCommSemigroup _ toAbsRelCycle_inj (λ _ _ ↦ rfl)
instance : SMul ℝ>0 (UsualEngineCycle 𝓒_lt_𝓗) where
  smul := fun c H ↦ {
    c • H.toAbsRelCycle,
    @Cycle.engine_smul_pos H.toCycle _ _ ⟨c.property⟩ with
  }

-- TODO : equivalence classes of `UsualEngineCycle`
variable {H₁ H₂ : UsualEngineCycle 𝓒_lt_𝓗}
lemma eq_smul_pos_of_eff_eq (heff : H₁.eff = H₂.eff) : ∃ c : ℝ>0, H₁ = c • H₂ := by
  let c : ℝ>0 := {
    val := H₁.𝓦 / H₂.𝓦
    property := by have := H₁.do_work; have := H₂.do_work; positivity
  }
  refine ⟨c, symm <| ?_⟩
  apply toAbsRelCycle_inj; apply AbsRelCycle.eq_of_Qabs_𝓦_eq
  · calc (c • H₂).Qabs
      _ = c.val * H₂.toCycle.Qabs := Cycle.Qabs_smul_pos c.property
      _ = H₁.𝓦 / H₂.𝓦 * H₂.Qabs  := rfl
      _ = H₁.𝓦 /(H₂.𝓦 / H₂.Qabs) := by field_simp
      _ = H₁.𝓦 / H₂.eff           := rfl
      _ = H₁.𝓦 / H₁.eff           := by rw [heff]
      _ = H₁.𝓦 /(H₁.𝓦 / H₁.Qabs) := rfl
      _ = H₁.Qabs := by
        field_simp [ne_of_gt Cycle.engine_do_work, Cycle.engine_do_abs]; ring
  · calc (c • H₂).𝓦
      _ = (c.val • H₂.toCycle).𝓦 := rfl
      _ = c.val * H₂.𝓦 := by simp
      _ = H₁.𝓦 / H₂.𝓦 * H₂.𝓦 := rfl
      _ = H₁.𝓦 := by field_simp [ne_of_gt Cycle.engine_do_work]

end UsualEngineCycle

/-!
### `UsualPumpCycle`
-/

/-- `AbsRelCycle`s that pump heat from colder `𝓒` to hotter `𝓗` -/
structure UsualPumpCycle {𝓒 𝓗 : Reservoir} (_: 𝓒 < 𝓗) extends (AbsRelCycle 𝓒 𝓗) where
  do_pump : toCycle.Qabs < toCycle.Qrel

namespace UsualPumpCycle
variable {𝓒 𝓗} {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H : UsualPumpCycle 𝓒_lt_𝓗}

lemma consume_work : H.𝓦 < 0 := AbsRelCycle.Qabs_lt_Qrel_iff_consume_work.mp H.do_pump

lemma toAbsRelCycle_inj :
  Function.Injective (fun H : UsualPumpCycle 𝓒_lt_𝓗 ↦ H.toAbsRelCycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩ ↦ by simp
instance : Add (UsualPumpCycle 𝓒_lt_𝓗) where
  add := fun H₁ H₂ ↦ {
    H₁.toAbsRelCycle + H₂.toAbsRelCycle with
    do_pump := by
      apply AbsRelCycle.Qabs_lt_Qrel_iff_consume_work.mpr
      calc (H₁.toAbsRelCycle + H₂.toAbsRelCycle).𝓦
        _ = H₁.𝓦 + H₂.𝓦 := Cycle.𝓦_add
        _ < 0 := by
          have := H₁.consume_work; have := H₂.consume_work
          linarith
  }
instance : AddCommSemigroup (UsualPumpCycle 𝓒_lt_𝓗) :=
  Function.Injective.addCommSemigroup _ toAbsRelCycle_inj (λ _ _ ↦ rfl)
instance : SMul ℝ>0 (UsualPumpCycle 𝓒_lt_𝓗) where
  smul := fun c H ↦ {
    c • H.toAbsRelCycle with
    do_pump := by
      apply AbsRelCycle.Qabs_lt_Qrel_iff_consume_work.mpr
      calc (c • H.toAbsRelCycle).𝓦
        _ = c * H.𝓦 := Cycle.𝓦_smul
        _ < 0 := mul_neg_of_pos_of_neg c.property H.consume_work
  }

end UsualPumpCycle

/-!
### Reverse of `UsualEngineCycle` and `UsualPumpCycle`
-/

section RevUsualEnginePumpCycle
variable {𝓒 𝓗 : Reservoir} {𝓒_lt_𝓗 : 𝓒 < 𝓗}

/-- The reverse of an `UsualEngineCycle` is an `UsualPumpCycle`. -/
@[reducible] def UsualEngineCycle.rev (H : UsualEngineCycle 𝓒_lt_𝓗) : UsualPumpCycle 𝓒_lt_𝓗 := {
  H.toAbsRelCycle.rev with
  do_pump := by
    apply AbsRelCycle.Qabs_lt_Qrel_iff_consume_work.mpr
    calc H.toAbsRelCycle.rev.𝓦
      _ = (-H.toCycle).𝓦 := rfl
      _ = -H.𝓦 := by simp
      _ < 0 := by simp [Cycle.engine_do_work]
}
/-- The reverse of an `UsualPumpCycle` is an `UsualEngineCycle`. -/
@[reducible] def UsualPumpCycle.rev (H : UsualPumpCycle 𝓒_lt_𝓗) : UsualEngineCycle 𝓒_lt_𝓗 := {
  H.toAbsRelCycle.rev with
  do_work := calc H.toAbsRelCycle.rev.𝓦
    _ = (-H.toCycle).𝓦 := rfl
    _ = -H.𝓦 := by simp
    _ > 0 := by simp [UsualPumpCycle.consume_work]
}

end RevUsualEnginePumpCycle

end Thermodynamics
