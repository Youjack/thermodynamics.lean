/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import second_law

/-!
# Characterization of `cycle.possible`

TODO
* characterization of possible `usual_engine_cycle` and `usual_pump_cycle`
* sufficient(equivalent) conditions for `cycle.possible` ?
-/

namespace thermodynamics

/-!
### `engine_cycle`
-/

namespace cycle
variables {H : cycle} [engine_cycle H]

lemma abs_every_rsv_if_no_rel (hno_rel : (H.Qrel:β) = 0) {π} (hπsupp : π β H.π .support) :
  0 < H.π  π := by {
  by_contradiction this, have := eq_or_lt_of_not_lt this,
  cases this with hπzero hπneg,
  { have := (H.π .mem_support_to_fun π).elim_left hπsupp,
    exact absurd hπzero this.symm, },
  { have : max (- H.π  π) 0 = - H.π  π, from max_eq_left_of_lt (neg_pos_of_neg hπneg),
    have :=
      calc βH.Qrel
           = H.π .support.sum (Ξ» π£, max (- H.π  π£) 0) : rfl
        ...= - H.π  π + (H.π .support.erase π).sum (Ξ» π£, max (- H.π  π£) 0) :
              by rw [βfinset.add_sum_erase _ _ hπsupp, this]
        ...β₯ - H.π  π :
              by simp only [finset.sum_nonneg, ge_iff_le, le_neg_add_iff_add_le, add_right_neg,
                            le_max_iff, le_refl, or_true, implies_true_iff]
        ...> 0 : neg_pos_of_neg hπneg,
    exact absurd hno_rel (ne_of_gt this), }, }
theorem psbl_engine_do_rel (hHpsbl : H.possible) : 0 < H.Qrel := by {
  suffices h : Ξ  n : β, (H.π .support.card = n.succ) β (0 < H.Qrel),
  { exact if hcard : H.π .support.card = 0 then by {
      have : H.π .support = β, from finset.card_eq_zero.elim_left hcard,
      have :=
        calc H.π¦
             = H.π .sum_image : H.π¦_from_π 
          ...= 0             : by rw [finsupp.sum_image, this, finset.sum_empty],
      exact absurd this (ne_of_gt H.engine_do_work), }
    else
      let β¨k, hkβ© := nat.exists_eq_succ_of_ne_zero hcard in
      h k hk },
  assume n, unfreezingI{revert H}, induction n with n ih,
  { assume H engH hHpsbl, haveI := engH, assume hcard,
    exact
    let β¨π£, hπ£β© := finset.card_eq_one.elim_left hcard in
    let H' : one_rsv_cycle π£ :=
      { to_cycle := H,
        one_rsv := hπ£ } in by {
    have hdo_work : 0 < H'.π¦ , from H.engine_do_work,
    have hpsbl : H'.possible, from hHpsbl,
    exact absurd hpsbl (kelvin_stmt H' hdo_work), } },
  { assume H engH hHpsbl, haveI := engH, assume hcard,
    by_contradiction hQrel, have hQrel := eq_of_ge_of_not_gt H.Qrel.property hQrel,
    have supp_nonempty := finset.card_pos.elim_left (by { rw hcard, exact nat.succ_pos' }),
    let π := H.π .support.min' supp_nonempty,
    let π := H.π .support.max' supp_nonempty,
    have π_supp : π β H.π .support, from finset.min'_mem _ _,
    have π_supp : π β H.π .support, from finset.max'_mem _ _,
    have do_absπ : 0 < H.π  π, from abs_every_rsv_if_no_rel hQrel π_supp,
    have do_absπ : 0 < H.π  π, from abs_every_rsv_if_no_rel hQrel π_supp,
    have π_lt_π : π < π, {
      have : 1 < H.π .support.card,
        rw hcard,
        apply nat.succ_lt_succ,
        exact nat.succ_pos',
      exact finset.min'_lt_max'_of_card _ this, },
    exact
    let β¨eng, heng, hQβ© := usual_engine_cycle.exists_psbl_rel π_lt_π do_absπ in
    let H' := H + eng.to_cycle in by {
    haveI : engine_cycle H' :=
      β¨ calc H'.π¦
             = H.π¦ + eng.π¦ : cycle.π¦_add
          ...> 0             : add_pos H.engine_do_work eng.do_work β©,
    have H'no_π :=
      calc H'.π  π
           = H.π  π + eng.π  π    : rfl
        ...= eng.Qrel + eng.π  π : by rw hQ
        ...= 0                  : by rw [eng.Qrel_one_rsv, add_left_neg],
    have H'do_absπ :=
      calc H'.π  π
         = H.π  π + eng.π  π : rfl
      ...= H.π  π + eng.Qabs : by rw eng.Qabs_one_rsv
      ...> 0                 : add_pos do_absπ eng.do_abs,
    have eng_Hsupp : H.π .support βͺ eng.π .support = H.π .support, {
      apply finset.union_eq_left_iff_subset.elim_right,
      rw eng.two_rsv.elim_left,
      apply finset.subset_iff.elim_right,
      simp only [finset.mem_insert, finset.mem_singleton],
      simp only [forall_eq_or_imp, forall_eq],
      exact β¨π_supp, π_suppβ©, },
    have lemmaH' : β {π£}, (π£ β  π) β (π£ β H.π .support) β (0 < H'.π  π£), {
      assume π£ hπ£notπ hπ£_Hsupp,
      exact if hπ£_π : π£ = π then by {
        rw hπ£_π, exact H'do_absπ, }
      else by {
        have : eng.π  π£ = 0, {
          apply finsupp.not_mem_support_iff.elim_left,
          rw [eng.two_rsv.elim_left, finset.mem_insert, finset.mem_singleton],
          simp only [hπ£notπ, hπ£_π, or_self, not_false_iff], },
        calc H'.π  π£
             = H.π  π£ + eng.π  π£ : rfl
          ...= H.π  π£           : by simp only [this, add_zero]
          ...> 0               : abs_every_rsv_if_no_rel hQrel hπ£_Hsupp, } },
    have H'supp_eraseπ : H'.π .support = H.π .support.erase π, {
      have : H'.π  = H.π  + eng.π , from rfl, rw this,
      apply finsupp.support_add_exact,
      { simp only [finset.mem_erase, ne.def, and_imp],
        assume π£ hπ£notπ hπ£_Hsupp,
        exact ne_of_gt (lemmaH' hπ£notπ hπ£_Hsupp), },
      { rw [eng_Hsupp, finset.sdiff_erase π_supp],
        simp only [finset.mem_singleton, forall_eq],
        exact H'no_π, } },
    have hH'no_rel : H'.Qrel.val = 0, {
      apply finset.sum_eq_zero,
      rw H'supp_eraseπ,
      simp only [finset.mem_erase, ne.def, max_eq_right_iff, right.neg_nonpos_iff, and_imp],
      assume π£ hπ£notπ hπ£_Hsupp,
      exact le_of_lt (lemmaH' hπ£notπ hπ£_Hsupp), },
    exact absurd hH'no_rel (ne_of_gt (@ih
      H' _
      (cycle.possible_add hHpsbl heng)
      ( calc H'.π .support.card
           = (H.π .support.erase π).card : by rw H'supp_eraseπ
        ...= H.π .support.card - 1       : finset.card_erase_of_mem π_supp
        ...= n.succ                     : by rw [hcard, nat.succ_sub_one] ) ) ), } } }
theorem psbl_engine_eff_lt_one (hHpsbl : H.possible) : H.eff < 1 := by {
  rw H.eff_from_Qabs_Qrel,
  have : (0:β) < H.Qrel / H.Qabs, from div_pos (psbl_engine_do_rel hHpsbl) H.engine_do_abs,
  simp only [this, sub_lt_self_iff], }
--

end cycle

end thermodynamics
