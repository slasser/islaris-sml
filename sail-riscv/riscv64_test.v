(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import SailStdpp.Base.
Require Import SailStdpp.State_monad.
Require Import SailStdpp.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
Require Import isla.sail_riscv.tactics.
Require Import isla.automation.
Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.
Require Import isla.examples.riscv64_test.

(* Deal with unification problem; upstream to stdpp *)
Global Hint Extern 10 (BvUnfold _ _ _ (@BV _ _ _) _) => apply bv_unfold_BV : bv_unfold_db.

Lemma sim_instr_a0:
  sim_instr (Uncompressed (BV 32 0x00000513)) a0.
Proof.
  move => regs. unfold step_cpu, a0.
  red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
  - by apply bv_eq.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed (BV 32 0x00150513)) a4.
Proof.
  move => regs. unfold step_cpu, a4. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
Qed.

Lemma sim_instr_a8:
  sim_instr (Uncompressed (BV 32 0x00b13423)) a8.
Proof.
  move => regs. unfold step_cpu, a8. red_sim. unfold execute. red_sim.
  unfold execute_STORE. red_sim. sim_simpl_regs.
  rewrite if_false; [|shelve]. red_sim.
  unfold translateAddr. red_sim. sim_simpl_regs.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold translationMode. sim_simpl_regs.
  have -> : (register_lookup cur_privilege regs) = Machine by destruct (register_lookup cur_privilege regs).
  unfold write_kind_of_flags. red_sim.
  unfold mem_write_value, mem_write_value_meta. red_sim.
  apply: sim_read_reg_l. red_sim.
  apply: sim_read_reg_l. red_sim. sim_simpl_regs.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold phys_access_check.
  rewrite Hassume. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  unfold write_kind_of_flags. red_sim.
  unfold ext_check_phys_mem_write. red_sim.
  Unshelve. all: sim_simpl_goal.
  - apply check_misaligned_false. rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv.
    by rewrite bv_extract_0_bv_add_distr // Hassume11.
  - by rewrite Hassume.
  - eapply within_mmio_writable_false.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, Hassume5, Hassume6, Hassume7, !bv_add_unsigned, !bv_unsigned_BV in *.
      rewrite /regtype/xlenbits/bits.
      lia.
  - eapply within_phys_mem_true.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + move: Hassume13. move: Hassume11 => /bv_eq. rewrite bv_extract_0_unsigned.
      rewrite ->Hassume1, Hassume2, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *.
      (* TODO: Why is this necessary? *)
      change (2 + 1 - 0)%N with (3%N).
      rewrite /regtype/xlenbits/bits.
      lia.
  Unshelve. all: exact: inhabitant.
Qed.

Lemma sim_instr_ac:
  sim_instr (Uncompressed (BV 32 0x00813583)) ac.
Proof.
  move => regs. unfold step_cpu, ac. red_sim. unfold execute. red_sim.
  unfold execute_LOAD. red_sim.
  rewrite if_false; [|shelve]. red_sim.
  unfold translateAddr. red_sim. sim_simpl_regs.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold translationMode. sim_simpl_regs.
  have -> : (register_lookup cur_privilege regs) = Machine by destruct (register_lookup cur_privilege regs). red_sim.
  unfold mem_read. red_sim.
  apply: sim_read_reg_l. red_sim.
  apply: sim_read_reg_l. red_sim. sim_simpl_regs.
  apply sim_effectivePrivilege; [done|]. red_sim.
  unfold phys_access_check.
  rewrite Hassume. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite /regtype/xlenbits/bits.
  - apply check_misaligned_false. rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv.
    by rewrite bv_extract_0_bv_add_distr // Hassume11.
  - rewrite Hassume //.
  - eapply within_mmio_writable_false.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + rewrite ->Hassume1, Hassume2, Hassume5, Hassume6, Hassume7, !bv_add_unsigned, !bv_unsigned_BV in *.
      lia.
  - eapply within_phys_mem_true.
    + rewrite mword_to_bv_add_vec; [|done]. reduce_closed_mword_to_bv. done.
    + move: Hassume13. move: Hassume11 => /bv_eq. rewrite bv_extract_0_unsigned.
      rewrite ->Hassume1, Hassume2, !bv_add_unsigned, !bv_unsigned_BV in *.
      unfold bv_wrap, bv_modulus in *.
      (* TODO: Why is this necessary? *)
      change (2 + 1 - 0)%N with (3%N).
      lia.
  Unshelve. all: exact: inhabitant.
Qed.

Lemma sim_instr_a10:
  sim_instr (Uncompressed (BV 32 0x00b50463)) a10.
Proof.
  move => regs. unfold step_cpu, a10. red_sim. unfold execute; red_sim.
  unfold execute_BTYPE; red_sim.
  apply: sim_read_reg_l; red_sim.
  sim_simpl_regs.
  destruct (eq_vec (@register_lookup regtype x10 regs) (@register_lookup regtype x11 regs)) eqn: Hb1; sim_simpl_hyp Hb1.
  - apply: (sim_tcases 0); [done|]. red_sim.
    rewrite bit_to_bool_false; [|shelve]. red_sim.
  - apply: (sim_tcases 1); [done|]. red_sim.
  Unshelve. all: sim_simpl_goal.
  + rewrite access_vec_dec_to_bv // bitU_of_bool_B0 //.
    rewrite mword_to_bv_add_vec //=. reduce_closed_mword_to_bv.
    bv_simplify. rename select (bv_extract 1 _ _ = _) into He. bv_simplify He.
    bitblast. by bitblast He with 0.
Qed.

Definition riscv_test_sail_instrs : gmap addr encoded_instruction :=
  <[ (BV 64 0x0000000010300000) := Uncompressed (BV 32 0x00000513)]> $
  <[ (BV 64 0x0000000010300004) := Uncompressed (BV 32 0x00150513)]> $
  <[ (BV 64 0x0000000010300008) := Uncompressed (BV 32 0x00b13423)]> $
  <[ (BV 64 0x000000001030000c) := Uncompressed (BV 32 0x00813583)]> $
  <[ (BV 64 0x0000000010300010) := Uncompressed (BV 32 0x00b50463)]> $
  ∅.

Definition riscv_test_initial_sail_state (x2v : bv 64) (regs : regstate) : sail_state :=
  SAIL (Interface.Ret tt) regs (riscv_test_state_global x2v).(seq_mem) riscv_test_sail_instrs false.

Lemma riscv_test_safe regs (satpv x10v x2v mstatus_bits x11v : bv 64):
  sys_pmp_count () = 0 →
  plat_enable_misaligned_access () = false →
  mword_to_bv (plat_ram_base ()) = (BV 64 0x0000000080000000) →
  mword_to_bv (plat_ram_size ()) = (BV 64 0x0000000004000000) →
  mword_to_bv (plat_rom_base ()) = (BV 64 0x0000000000001000) →
  mword_to_bv (plat_rom_size ()) = (BV 64 0x0000000000000100) →
  mword_to_bv (plat_clint_base ()) = (BV 64 0x0000000002000000) →
  mword_to_bv (plat_clint_size ()) = (BV 64 0x00000000000c0000) →
  mword_to_bv (plat_htif_tohost ()) = (BV 64 0x0000000040001000) →
  Z.land (bv_unsigned mstatus_bits) 0x20000 = 0 →
  bv_unsigned x2v `mod` 8 = 0 →
  bv_unsigned x2v + 16 < 2 ^ 64 →
  0x0000000080000000 ≤ bv_unsigned x2v + 8 < 0x0000000080000000 + 0x0000000004000000 →
  register_lookup PC regs = bv_to_mword (BV 64 0x0000000010300000) →
  register_lookup x2 regs = bv_to_mword x2v →
  register_lookup x10 regs = bv_to_mword x10v →
  register_lookup x11 regs = bv_to_mword x11v →
  register_lookup satp regs = bv_to_mword satpv →
  register_lookup cur_privilege regs = Machine →
  register_lookup misa regs = misa_bits →
  register_lookup mstatus regs = mstatus_bits →
  safe sail_module (riscv_test_initial_sail_state x2v regs) ∧
    (∀ κs σ', steps sail_module (riscv_test_initial_sail_state x2v regs) κs σ' → riscv_test_spec x11v κs).
Proof.
  move => Hpmp ????????? ??? HPC Hx2 Hx10 Hx11 Hsatp Hcur_priv Hmisa Hmstatus.
  apply: iris_transfer_refines.
  { apply iris_module_wf_isla_lang. }
  { move => ????. by apply (riscv_test_adequate mstatus_bits satpv x2v x10v x11v). }
  eapply sim_implies_refines.
  - rewrite !dom_insert_L !dom_empty_L. set_solver.
  - move => ??.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq => //.
    all: unfold get_regval_or_config; simpl; sim_simpl_goal.
    + by rewrite Hpmp.
    + by rewrite Hcur_priv.
  - done.
  - unfold riscv_test_sail_instrs. move => ??? Hsail.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq.
    + apply sim_instr_a0.
    + apply sim_instr_a4.
    + apply sim_instr_a8.
    + apply sim_instr_ac.
    + apply sim_instr_a10.
Qed.

(* Print Assumptions riscv_test_safe. *)
